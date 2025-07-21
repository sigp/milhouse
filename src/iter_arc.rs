use tree_hash::{TreeHash, TreeHashType};
use triomphe::Arc;

use crate::{
    Error, Leaf, Tree, UpdateMap, Value,
    utils::{Length, opt_packing_depth},
};

#[derive(Debug)]
pub struct ArcIter<'a, T: Value> {
    /// Stack of tree nodes corresponding to the current position.
    stack: Vec<&'a Tree<T>>,
    /// The list index corresponding to the current position (next element to be yielded).
    index: usize,
    /// The `depth` of the root tree.
    full_depth: usize,
    /// Cached packing depth to avoid re-calculating `opt_packing_depth`.
    packing_depth: usize,
    /// Number of items that will be yielded by the iterator.
    length: Length,
}

impl<'a, T: Value> ArcIter<'a, T> {
    pub fn from_index(
        index: usize,
        root: &'a Tree<T>,
        depth: usize,
        length: Length,
    ) -> Result<Self, Error> {
        if <T as TreeHash>::tree_hash_type() == TreeHashType::Basic {
            return Err(Error::PackedLeavesNoArc);
        }
        let mut stack = Vec::with_capacity(depth);
        stack.push(root);

        Ok(ArcIter {
            stack,
            index,
            full_depth: depth,
            packing_depth: opt_packing_depth::<T>().unwrap_or(0),
            length,
        })
    }
}

impl<'a, T: Value> ArcIter<'a, T> {
    pub fn new(root: &'a Tree<T>, depth: usize, length: Length) -> Self {
        let mut stack = Vec::with_capacity(depth);
        stack.push(root);

        ArcIter {
            stack,
            index: 0,
            full_depth: depth,
            packing_depth: opt_packing_depth::<T>().unwrap_or(0),
            length,
        }
    }
}

impl<'a, T: Value> Iterator for ArcIter<'a, T> {
    type Item = &'a Arc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.length.as_usize() {
            return None;
        }

        match self.stack.last() {
            None | Some(Tree::Zero(_)) => None,
            Some(Tree::Leaf(Leaf { value, .. })) => {
                let result = Some(value);

                self.index += 1;

                // Backtrack to the parent node of the next subtree
                for _ in 0..=self.index.trailing_zeros() {
                    self.stack.pop();
                }

                result
            }
            Some(Tree::PackedLeaf(_)) => {
                // Return None case of PackedLeaf
                None
            }
            Some(Tree::Node { left, right, .. }) => {
                let depth = self.full_depth - self.stack.len();

                // Go left
                if (self.index >> (depth + self.packing_depth)) & 1 == 0 {
                    self.stack.push(left);
                    self.next()
                }
                // Go right
                else {
                    self.stack.push(right);
                    self.next()
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.as_usize().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<T: Value> ExactSizeIterator for ArcIter<'_, T> {}
#[derive(Debug)]
pub struct ArcInterfaceIter<'a, T: Value, U: UpdateMap<T>> {
    tree_iter: ArcIter<'a, T>,
    updates: &'a U,
    index: usize,
    length: usize,
}

impl<'a, T: Value, U: UpdateMap<T>> ArcInterfaceIter<'a, T, U> {
    pub fn new(root: &'a Tree<T>, depth: usize, length: Length, updates: &'a U) -> Self {
        ArcInterfaceIter {
            tree_iter: ArcIter::new(root, depth, length),
            updates,
            index: 0,
            length: length.as_usize(),
        }
    }
}

impl<'a, T: Value, U: UpdateMap<T>> Iterator for ArcInterfaceIter<'a, T, U> {
    type Item = Arc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.length {
            return None;
        }
        let idx = self.index;
        self.index += 1;

        let backing = self.tree_iter.next();
        if let Some(new_val) = self.updates.get(idx) {
            Some(
                self.updates
                    .get_arc(idx)
                    .unwrap_or_else(|| Arc::new(new_val.clone())),
            )
        } else {
            backing.cloned()
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.length.saturating_sub(self.index);
        (rem, Some(rem))
    }
}
impl<T: Value, U: UpdateMap<T>> ExactSizeIterator for ArcInterfaceIter<'_, T, U> {}
