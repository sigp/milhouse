use crate::{
    utils::{opt_packing_depth, opt_packing_factor},
    Leaf, PackedLeaf, Tree,
};
use tree_hash::TreeHash;

#[derive(Debug)]
pub struct Iter<'a, T: TreeHash + Clone> {
    /// Stack of tree nodes corresponding to the current position.
    stack: Vec<&'a Tree<T>>,
    /// The list index corresponding to the current position (next element to be yielded).
    index: usize,
    /// The `depth` of the root tree.
    full_depth: usize,
    /// Cached packing factor to avoid re-calculating `opt_packing_factor`.
    ///
    /// Initialised to 0 if `T` is not packed.
    packing_factor: usize,
    /// Cached packing depth to avoid re-calculating `opt_packing_depth`.
    packing_depth: usize,
    /// Number of items that will be yielded by the iterator.
    length: usize,
}

impl<'a, T: TreeHash + Clone> Iter<'a, T> {
    pub fn from_index(index: usize, root: &'a Tree<T>, depth: usize, length: usize) -> Self {
        let mut stack = Vec::with_capacity(depth);
        stack.push(root);

        Iter {
            stack,
            index,
            full_depth: depth,
            packing_factor: opt_packing_factor::<T>().unwrap_or(0),
            packing_depth: opt_packing_depth::<T>().unwrap_or(0),
            length,
        }
    }
}

impl<'a, T: TreeHash + Clone> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.length {
            return None;
        }

        match self.stack.last() {
            None | Some(Tree::Zero(_)) => None,
            Some(Tree::Leaf(Leaf { value, .. })) => {
                let result = Some(value.as_ref());

                self.index += 1;

                // Backtrack to the parent node of the next subtree
                for _ in 0..=self.index.trailing_zeros() {
                    self.stack.pop();
                }

                result
            }
            Some(Tree::PackedLeaf(PackedLeaf { values, .. })) => {
                let sub_index = self.index % self.packing_factor;

                let result = values.get(sub_index);

                self.index += 1;

                // Reached end of chunk
                if sub_index + 1 == self.packing_factor {
                    // FIXME(sproul): unwrap
                    let to_pop = self
                        .index
                        .trailing_zeros()
                        .checked_sub(self.packing_depth as u32)
                        .unwrap();

                    for _ in 0..=to_pop {
                        self.stack.pop();
                    }
                }

                result
            }
            Some(Tree::Node { left, right, .. }) => {
                let depth = self.full_depth - self.stack.len();

                // Go left
                if (self.index >> (depth + self.packing_depth)) & 1 == 0 {
                    self.stack.push(&left);
                    self.next()
                }
                // Go right
                else {
                    self.stack.push(&right);
                    self.next()
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, T: TreeHash + Clone> ExactSizeIterator for Iter<'a, T> {}
