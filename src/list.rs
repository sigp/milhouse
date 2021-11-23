use crate::interface::{ImmList, Interface, MutList, PushList};
use crate::iter::Iter;
use crate::utils::{borrow_mut, int_log};
use crate::{Error, Tree};
use std::marker::PhantomData;
use std::sync::Arc;
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

#[derive(Debug, PartialEq, Clone)]
pub struct List<T, N: Unsigned> {
    tree: Arc<Tree<T>>,
    length: usize,
    depth: usize,
    _phantom: PhantomData<N>,
}

impl<T: Clone, N: Unsigned> List<T, N> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }

    pub fn empty() -> Self {
        Self::try_from_iter(std::iter::empty()).unwrap()
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let leaves = iter.into_iter().map(Tree::leaf).collect::<Vec<_>>();
        if leaves.len() <= N::to_usize() {
            let length = leaves.len();
            let depth = int_log(N::to_usize());
            let tree = Tree::create(leaves, depth);
            Ok(Self {
                tree,
                length,
                depth,
                _phantom: PhantomData,
            })
        } else {
            Err(Error::Oops)
        }
    }

    pub fn as_mut(&mut self) -> Interface<T, &mut Self> {
        Interface::new(self)
    }

    pub fn iter(&self) -> Iter<T> {
        Iter::new(&self.tree, self.depth, self.length)
    }
}

impl<T: Clone, N: Unsigned> ImmList<T> for List<T, N> {
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            self.tree.get(index, self.depth)
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        self.length
    }
}

impl<'a, T: Clone, N: Unsigned> ImmList<T> for &'a mut List<T, N> {
    fn get<'s>(&'s self, index: usize) -> Option<&'s T> {
        borrow_mut(self).get(index)
    }

    fn len(&self) -> usize {
        borrow_mut(self).len()
    }
}

impl<'a, T, N> MutList<T> for &'a mut List<T, N>
where
    T: Clone,
    N: Unsigned,
{
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        Ok(())
    }
}

impl<'a, T, N> PushList<T> for &'a mut List<T, N>
where
    T: Clone,
    N: Unsigned,
{
    fn push(&mut self, value: T) -> Result<(), Error> {
        if self.length == N::to_usize() {
            return Err(Error::Oops);
        }
        let index = self.length;
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        self.length += 1;
        Ok(())
    }
}

impl<T: TreeHash + Clone, N: Unsigned> TreeHash for List<T, N> {
    fn tree_hash_type() -> tree_hash::TreeHashType {
        tree_hash::TreeHashType::List
    }

    fn tree_hash_packed_encoding(&self) -> Vec<u8> {
        unreachable!("List should never be packed.")
    }

    fn tree_hash_packing_factor() -> usize {
        unreachable!("List should never be packed.")
    }

    fn tree_hash_root(&self) -> Hash256 {
        let root = self.tree.tree_hash();
        tree_hash::mix_in_length(&root, self.len())
    }
}

impl<'a, T: Clone, N: Unsigned> IntoIterator for &'a List<T, N> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
