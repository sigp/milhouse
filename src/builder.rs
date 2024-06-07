use crate::utils::{opt_packing_depth, opt_packing_factor, Length, MaybeArced};
use crate::{Arc, Error, PackedLeaf, Tree, Value, MAX_TREE_DEPTH};

#[derive(Debug)]
pub struct Builder<T: Value> {
    stack: Vec<MaybeArced<Tree<T>>>,
    /// The depth of the tree excluding the packing depth.
    depth: usize,
    /// The level (depth) in the tree at which nodes
    level: usize,
    length: Length,
    /// Cached value of `opt_packing_factor`.
    packing_factor: Option<usize>,
    /// Cached value of `opt_packing_depth`.
    packing_depth: usize,
    /// Cached value of capacity: 2^(depth + packing_depth).
    capacity: usize,
}

impl<T: Value> Builder<T> {
    pub fn new(depth: usize, level: usize) -> Result<Self, Error> {
        let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
        if depth.saturating_add(packing_depth) > MAX_TREE_DEPTH {
            Err(Error::BuilderInvalidDepth { depth })
        } else {
            let capacity = 1 << (depth + packing_depth);
            Ok(Self {
                stack: Vec::with_capacity(depth),
                depth,
                level,
                length: Length(0),
                packing_factor: opt_packing_factor::<T>(),
                packing_depth,
                capacity,
            })
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        if self.length.as_usize() == self.capacity {
            return Err(Error::BuilderFull);
        }
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
        if self.length.as_usize() == self.capacity {
            return Err(Error::BuilderFull);
        }

        let index_on_level = self.length.as_usize() >> self.level;
        let next_index_on_level = index_on_level + 1;

        let mut new_stack_top = MaybeArced::Arced(node);

        // Subtract the packing depth if we are on level 0, in which case `next_index` includes
        // `packing_depth` trailing bits which don't correspond to stack entries and should not be
        // popped.
        let values_to_merge = if self.level == 0 {
            next_index_on_level
                .trailing_zeros()
                .saturating_sub(self.packing_depth as u32)
        } else {
            next_index_on_level.trailing_zeros()
        };

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

        let length = self.length.as_usize();
        let level_capacity = 1 << self.level;
        let mut next_index_on_level = (length + level_capacity - 1) / level_capacity;

        // Finish any partially-filled packed leaf.
        if let Some(packing_factor) = self.packing_factor {
            let skip_indices = packing_factor
                .saturating_sub(self.length.as_usize() % packing_factor)
                % packing_factor;

            if skip_indices > 0 && self.level == 0 {
                // If the packed leaf lies on the right, merge it with its left sibling and so
                // on up the tree.
                for i in 0..self.depth {
                    if (next_index_on_level >> (i + self.packing_depth)) & 1 == 1 {
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
                next_index_on_level += skip_indices;
            }
        }

        while next_index_on_level << self.level != self.capacity {
            // Push a new zero padding node on the right of the top-most stack element.
            let depth = (next_index_on_level.trailing_zeros() as usize)
                .saturating_add(self.level)
                .saturating_sub(self.packing_depth);

            let stack_top = self.stack.pop().ok_or(Error::BuilderStackEmptyFinish)?;
            let new_stack_top =
                MaybeArced::Unarced(Tree::node_unboxed(stack_top.arced(), Tree::zero(depth)));

            self.stack.push(new_stack_top);

            // Merge up to `depth` nodes if they exist on the stack.
            for i in depth + 1..self.depth {
                if ((next_index_on_level << self.level) >> (i + self.packing_depth)) & 1 == 1 {
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

            next_index_on_level += 2usize.pow((depth + self.packing_depth - self.level) as u32);
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn depth_upper_limit() {
        assert_eq!(
            Builder::<u64>::new(62, 0).unwrap_err(),
            Error::BuilderInvalidDepth { depth: 62 }
        );
        assert_eq!(Builder::<u64>::new(61, 0).unwrap().depth, 61);
    }
}
