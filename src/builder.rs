use crate::utils::{opt_packing_depth, opt_packing_factor, Length, MaybeArced};
use crate::{Arc, Error, PackedLeaf, Tree, Value};

pub struct Builder<T: Value> {
    stack: Vec<MaybeArced<Tree<T>>>,
    depth: usize,
    level: usize,
    length: Length,
    /// Cached value of `opt_packing_factor`.
    packing_factor: Option<usize>,
    /// Cached value of `opt_packing_depth`.
    packing_depth: usize,
}

impl<T: Value> Builder<T> {
    pub fn new(depth: usize, level: usize) -> Self {
        Self {
            stack: Vec::with_capacity(depth),
            depth,
            level,
            length: Length(0),
            packing_factor: opt_packing_factor::<T>(),
            packing_depth: opt_packing_depth::<T>().unwrap_or(0),
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        let index = self.length.as_usize();
        let next_index = index + 1;

        // Fold the nodes on the left of this node into it, and then push that node to the stack.
        let mut new_stack_top = if let Some(packing_factor) = self.packing_factor {
            if index % packing_factor == 0 {
                MaybeArced::Unarced(Tree::PackedLeaf(PackedLeaf::single(value)))
            } else if let Some(MaybeArced::Unarced(Tree::PackedLeaf(mut leaf))) = self.stack.pop() {
                leaf.push(value)?;
                MaybeArced::Unarced(Tree::PackedLeaf(leaf))
            } else {
                return Err(Error::BuilderExpectedLeaf);
            }
        } else {
            MaybeArced::Unarced(Tree::leaf_unboxed(value))
        };

        let values_to_merge = next_index
            .trailing_zeros()
            .saturating_sub(self.packing_depth as u32);

        for _ in 0..values_to_merge {
            let left = self.stack.pop().ok_or(Error::BuilderStackEmptyMerge)?;
            new_stack_top =
                MaybeArced::Unarced(Tree::node_unboxed(left.arced(), new_stack_top.arced()));
        }

        self.stack.push(new_stack_top);
        *self.length.as_mut() += 1;

        Ok(())
    }

    pub fn push_node(&mut self, node: Arc<Tree<T>>, len: usize) -> Result<(), Error> {
        let index = self.length.as_usize();
        let next_index = index + len;

        let mut new_stack_top = MaybeArced::Arced(node);

        assert_eq!(index % (1 << self.level), 0);

        let values_to_merge = next_index
            .trailing_zeros()
            .saturating_add(1)
            .saturating_sub(self.level as u32)
            .saturating_sub(self.packing_depth as u32);

        for _ in 0..values_to_merge {
            if let Some(left) = self.stack.pop() {
                new_stack_top =
                    MaybeArced::Unarced(Tree::node_unboxed(left.arced(), new_stack_top.arced()));
            }
        }

        self.stack.push(new_stack_top);
        *self.length.as_mut() += len;

        Ok(())
    }

    pub fn finish(mut self) -> Result<(Arc<Tree<T>>, usize, Length), Error> {
        if self.stack.is_empty() {
            return Ok((Tree::zero(self.depth), self.depth, Length(0)));
        }

        let capacity = 2usize.pow((self.depth + self.packing_depth) as u32);
        let mut next_index = self.length.as_usize();

        // Finish any partially-filled packed leaf.
        if let Some(packing_factor) = self.packing_factor {
            let skip_indices = packing_factor
                .saturating_sub(self.length.as_usize() % packing_factor)
                % packing_factor;

            if skip_indices > 0 {
                // If the packed leaf lies on the right, merge it with its left sibling and so
                // on up the tree.
                for i in 0..self.depth {
                    if (next_index >> (i + self.packing_depth)) & 1 == 1 {
                        let right = self.stack.pop().ok_or(Error::BuilderStackEmptyMergeRight)?;
                        let left = self.stack.pop().ok_or(Error::BuilderStackEmptyMergeLeft)?;
                        self.stack.push(MaybeArced::Unarced(Tree::node_unboxed(
                            left.arced(),
                            right.arced(),
                        )));
                    } else {
                        break;
                    }
                }
                next_index += skip_indices;
            }
        }

        while next_index != capacity {
            // Push a new zero padding node on the right of the top-most stack element.
            let depth = (next_index.trailing_zeros() as usize)
                .saturating_sub(self.level)
                .saturating_sub(self.packing_depth);

            let stack_top = self.stack.pop().ok_or(Error::BuilderStackEmptyFinish)?;
            let new_stack_top =
                MaybeArced::Unarced(Tree::node_unboxed(stack_top.arced(), Tree::zero(depth)));

            self.stack.push(new_stack_top);

            // Merge up to `depth` nodes if they exist on the stack.
            for i in depth + 1..self.depth {
                println!("{:?}", self.stack);
                if (next_index >> (i + self.packing_depth)) & 1 == 1 {
                    let right = self
                        .stack
                        .pop()
                        .ok_or(Error::BuilderStackEmptyFinishRight)?;
                    let left = self.stack.pop().ok_or(Error::BuilderStackEmptyFinishLeft)?;
                    self.stack.push(MaybeArced::Unarced(Tree::node_unboxed(
                        left.arced(),
                        right.arced(),
                    )));
                } else {
                    break;
                }
            }

            next_index += 2usize.pow((depth + self.packing_depth) as u32);
        }

        let tree = self
            .stack
            .pop()
            .ok_or(Error::BuilderStackEmptyFinalize)?
            .arced();

        if !self.stack.is_empty() {
            return Err(Error::BuilderStackLeftover);
        }

        Ok((tree, self.depth, self.length))
    }
}
