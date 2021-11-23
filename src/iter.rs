use crate::{Leaf, Tree};

pub struct Iter<'a, T> {
    pub(crate) stack: Vec<&'a Tree<T>>,
    pub(crate) index: u64,
    pub(crate) full_depth: usize,
    pub(crate) length: usize,
}

impl<'a, T> Iter<'a, T> {
    pub fn new(root: &'a Tree<T>, depth: usize, length: usize) -> Self {
        Iter {
            stack: vec![root],
            index: 0,
            full_depth: depth,
            length,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.stack.last() {
            None | Some(Tree::Zero(_)) => None,
            Some(Tree::Leaf(Leaf { value, .. })) => {
                let result = Some(value);

                self.index += 1;

                // Backtrack to the parent node of the next subtree
                self.stack.pop();
                for _ in 0..self.index.trailing_zeros() + 1 {
                    self.stack.pop();
                }

                result
            }
            Some(Tree::Node { left, right, .. }) => {
                let depth = self.full_depth - self.stack.len();

                // Go left
                if (self.index >> depth) & 1 == 0 {
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
        (self.length, Some(self.length))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}
