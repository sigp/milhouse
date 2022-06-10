use crate::cow::{BTreeCow, Cow};
use crate::utils::max_btree_index;
use std::collections::{btree_map::Entry, BTreeMap};
use std::ops::ControlFlow;

/// Trait for map types which can be used to store intermediate updates before application
/// to the tree.
pub trait UpdateMap<T>: Default + Clone {
    fn get(&self, k: usize) -> Option<&T>;

    fn get_mut_with<F>(&mut self, k: usize, f: F) -> Option<&mut T>
    where
        F: FnOnce(usize) -> Option<T>;

    fn get_cow_with<'a, F>(&'a mut self, k: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
        T: Clone + 'a;

    fn insert(&mut self, k: usize, value: T) -> Option<T>;

    fn for_each_range<F, E>(&self, start: usize, end: usize, f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>;

    fn max_index(&self) -> Option<usize>;

    fn len(&self) -> usize;

    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T: Clone> UpdateMap<T> for BTreeMap<usize, T> {
    fn get(&self, k: usize) -> Option<&T> {
        BTreeMap::get(self, &k)
    }

    fn get_mut_with<F>(&mut self, idx: usize, f: F) -> Option<&mut T>
    where
        F: FnOnce(usize) -> Option<T>,
    {
        match self.entry(idx) {
            Entry::Vacant(entry) => {
                // Copy on write.
                let value = f(idx)?;
                Some(entry.insert(value))
            }
            Entry::Occupied(entry) => Some(entry.into_mut()),
        }
    }

    fn get_cow_with<'a, F>(&'a mut self, idx: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
    {
        let cow = match self.entry(idx) {
            Entry::Vacant(entry) => {
                let value = f(idx)?;
                BTreeCow::Immutable { value, entry }
            }
            Entry::Occupied(entry) => BTreeCow::Mutable {
                value: entry.into_mut(),
            },
        };
        Some(Cow::BTree(cow))
    }

    fn insert(&mut self, idx: usize, value: T) -> Option<T> {
        BTreeMap::insert(self, idx, value)
    }

    fn for_each_range<F, E>(&self, start: usize, end: usize, mut f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>,
    {
        for (key, value) in self.range(start..end) {
            match f(*key, value) {
                ControlFlow::Continue(res) => res?,
                ControlFlow::Break(()) => break,
            }
        }
        Ok(())
    }

    fn max_index(&self) -> Option<usize> {
        max_btree_index(self)
    }

    fn len(&self) -> usize {
        BTreeMap::len(self)
    }
}
