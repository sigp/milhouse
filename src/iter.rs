use crate::{utils::opt_packing_depth, Leaf, PackedLeaf, Tree};
use tree_hash::TreeHash;

pub struct Iter<'a, T: TreeHash + Clone> {
    pub(crate) stack: Vec<&'a Tree<T>>,
    pub(crate) index: u64,
    pub(crate) full_depth: usize,
    pub(crate) length: usize,
}

impl<'a, T: TreeHash + Clone> Iter<'a, T> {
    pub fn new(root: &'a Tree<T>, depth: usize, length: usize) -> Self {
        Iter {
            stack: vec![root],
            index: 0,
            full_depth: depth,
            length,
        }
    }
}

impl<'a, T: TreeHash + Clone> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
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
            Some(Tree::PackedLeaf(PackedLeaf { values, .. })) => {
                let packing_factor = T::tree_hash_packing_factor();
                let sub_index = self.index as usize % packing_factor;

                let result = values.get(sub_index);

                self.index += 1;

                // Reached end of chunk
                if sub_index + 1 == packing_factor {
                    // FIXME(sproul): unwrap
                    let to_pop = self
                        .index
                        .trailing_zeros()
                        .checked_sub(opt_packing_depth::<T>().unwrap() as u32)
                        .unwrap();

                    for _ in 0..=to_pop {
                        self.stack.pop();
                    }
                }

                result
            }
            Some(Tree::Node { left, right, .. }) => {
                let depth = self.full_depth - self.stack.len();
                let packing_depth = opt_packing_depth::<T>().unwrap_or(0);

                // Go left
                if (self.index >> (depth + packing_depth)) & 1 == 0 {
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

impl<'a, T: TreeHash + Clone> ExactSizeIterator for Iter<'a, T> {}
