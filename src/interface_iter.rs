use crate::cow::Cow;
use crate::iter::Iter;
use std::collections::{btree_map::Entry, BTreeMap};
use tree_hash::TreeHash;

#[derive(Debug)]
pub struct InterfaceIter<'a, T: TreeHash + Clone> {
    pub(crate) tree_iter: Iter<'a, T>,
    pub(crate) updates: &'a BTreeMap<usize, T>,
    pub(crate) index: usize,
    pub(crate) length: usize,
}

impl<'a, T: TreeHash + Clone> Iterator for InterfaceIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        if self.tree_iter.index < self.tree_iter.length {
            assert_eq!(self.tree_iter.index, index);
        }
        let backing_value = self.tree_iter.next();

        // Prioritise the value from the update map.
        self.updates.get(&index).or(backing_value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, T: TreeHash + Clone> ExactSizeIterator for InterfaceIter<'a, T> {}

#[derive(Debug)]
pub struct InterfaceIterCow<'a, T: TreeHash + Clone> {
    pub(crate) tree_iter: Iter<'a, T>,
    pub(crate) updates: &'a mut BTreeMap<usize, T>,
    pub(crate) index: usize,
}

impl<'a, T: TreeHash + Clone> InterfaceIterCow<'a, T> {
    pub fn next_cow(&mut self) -> Option<(usize, Cow<T>)> {
        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        if self.tree_iter.index < self.tree_iter.length {
            assert_eq!(self.tree_iter.index, index);
        }
        let backing_value = self.tree_iter.next();

        // Construct a CoW pointer using the updated entry from the map, or the corresponding
        // vacant entry and the value from the backing iterator.
        let cow = match self.updates.entry(index) {
            Entry::Occupied(entry) => Cow::Mutable {
                value: entry.into_mut(),
            },
            Entry::Vacant(entry) => Cow::Immutable {
                value: backing_value?,
                entry,
            },
        };
        Some((index, cow))
    }
}
