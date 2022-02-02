use crate::utils::{opt_packing_depth, opt_packing_factor};
use crate::{Error, PackedLeaf, Tree};
use std::sync::Arc;
use tree_hash::TreeHash;

pub struct Builder<T: TreeHash + Clone> {
    stack: Vec<Tree<T>>,
    depth: usize,
    length: usize,
}

impl<T: TreeHash + Clone> Builder<T> {
    pub fn new(depth: usize) -> Self {
        Self {
            stack: Vec::with_capacity(depth),
            depth,
            length: 0,
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        let index = self.length;
        let next_index = index + 1;

        // Fold the nodes on the left of this node into it, and then push that node to the stack.
        let mut new_stack_top = if let Some(packing_factor) = opt_packing_factor::<T>() {
            if index % packing_factor == 0 {
                Tree::PackedLeaf(PackedLeaf::single(value))
            } else if let Some(Tree::PackedLeaf(mut leaf)) = self.stack.pop() {
                leaf.push(value)?;
                Tree::PackedLeaf(leaf)
            } else {
                return Err(Error::Oops);
            }
        } else {
            Tree::leaf_unboxed(value)
        };

        let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
        let values_to_merge = next_index
            .trailing_zeros()
            .saturating_sub(packing_depth as u32);

        for _ in 0..values_to_merge {
            let left = self.stack.pop().ok_or(Error::Oops)?;
            new_stack_top = Tree::node_unboxed(Arc::new(left), Arc::new(new_stack_top));
        }

        self.stack.push(new_stack_top);
        self.length += 1;

        Ok(())
    }

    pub fn finish(mut self) -> Result<(Arc<Tree<T>>, usize, usize), Error> {
        if self.stack.len() == 0 {
            return Ok((Tree::zero(self.depth), self.depth, 0));
        }

        let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
        let capacity = 2usize.pow((self.depth + packing_depth) as u32);
        let mut next_index = self.length;

        // Finish any partially-filled packed leaf.
        if let Some(packing_factor) = opt_packing_factor::<T>() {
            let skip_indices =
                packing_factor.saturating_sub(self.length % packing_factor) % packing_factor;

            if skip_indices > 0 {
                // If the packed leaf lies on the right, merge it with its left sibling and so
                // on up the tree.
                for i in 0..self.depth {
                    if (next_index >> (i + packing_depth)) & 1 == 1 {
                        let right = self.stack.pop().ok_or(Error::Oops)?;
                        let left = self.stack.pop().ok_or(Error::Oops)?;
                        self.stack
                            .push(Tree::node_unboxed(Arc::new(left), Arc::new(right)));
                    } else {
                        break;
                    }
                }
                next_index += skip_indices;
            }
        }

        while next_index != capacity {
            // Push a new zero padding node on the right of the top-most stack element.
            let depth = (next_index.trailing_zeros() as usize).saturating_sub(packing_depth);

            let stack_top = self.stack.pop().ok_or(Error::Oops)?;
            let new_stack_top = Tree::node_unboxed(Arc::new(stack_top), Tree::zero(depth));

            self.stack.push(new_stack_top);

            // Merge up to `depth` nodes if they exist on the stack.
            for i in depth + 1..self.depth {
                if (next_index >> (i + packing_depth)) & 1 == 1 {
                    let right = self.stack.pop().ok_or(Error::Oops)?;
                    let left = self.stack.pop().ok_or(Error::Oops)?;
                    self.stack
                        .push(Tree::node_unboxed(Arc::new(left), Arc::new(right)));
                } else {
                    break;
                }
            }

            next_index += 2usize.pow((depth + packing_depth) as u32);
        }

        if self.stack.len() != 1 {
            return Err(Error::Oops);
        }

        let tree = Arc::new(self.stack.pop().ok_or(Error::Oops)?);
        Ok((tree, self.depth, self.length))
    }
}
