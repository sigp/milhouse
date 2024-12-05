use crate::iter::Iter;
use crate::{Cow, UpdateMap, Value};

#[derive(Debug)]
pub struct InterfaceIter<'a, T: Value, U: UpdateMap<T>> {
    pub(crate) tree_iter: Iter<'a, T>,
    pub(crate) updates: &'a U,
    pub(crate) index: usize,
    pub(crate) length: usize,
}

impl<'a, T: Value, U: UpdateMap<T>> Iterator for InterfaceIter<'a, T, U> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        let backing_value = self.tree_iter.next();

        // Prioritise the value from the update map.
        self.updates.get(index).or(backing_value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<T: Value, U: UpdateMap<T>> ExactSizeIterator for InterfaceIter<'_, T, U> {}

#[derive(Debug)]
pub struct InterfaceIterCow<'a, T: Value, U: UpdateMap<T>> {
    pub(crate) tree_iter: Iter<'a, T>,
    pub(crate) updates: &'a mut U,
    pub(crate) index: usize,
}

impl<T: Value, U: UpdateMap<T>> InterfaceIterCow<'_, T, U> {
    pub fn next_cow(&mut self) -> Option<(usize, Cow<T>)> {
        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        let backing_value = self.tree_iter.next();

        // Construct a CoW pointer using the updated entry from the map, or the corresponding
        // vacant entry and the value from the backing iterator.
        let cow = self.updates.get_cow_with(index, |_| backing_value)?;
        Some((index, cow))
    }
}
