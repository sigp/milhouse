use triomphe::Arc;

use crate::{
    utils::{opt_packing_depth, Length},
    Leaf, Tree, Value,
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
    pub fn from_index(index: usize, root: &'a Tree<T>, depth: usize, length: Length) -> Self {
        let mut stack = Vec::with_capacity(depth);
        stack.push(root);

        ArcIter {
            stack,
            index,
            full_depth: depth,
            packing_depth: opt_packing_depth::<T>().unwrap_or(0),
            length,
        }
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
            length: length,
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
                // Panic in case of PackedLeaf
                panic!("Arc iterator encountered packed leaves, but TreeHashType check should prevent this");
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
