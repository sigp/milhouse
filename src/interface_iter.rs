use crate::iter::Iter;
use crate::{Cow, UpdateMap, Value};
use parking_lot::RwLockWriteGuard;

#[derive(Debug)]
pub struct InterfaceIter<'a, T: Value> {
    pub(crate) tree_iter: Iter<'a, T>,
    // FIXME(sproul): remove write guard and flush updates prior to iteration?
    // pub(crate) updates: RwLockWriteGuard<'a, U>,
    pub(crate) index: usize,
    pub(crate) length: usize,
}

impl<'a, T: Value> Iterator for InterfaceIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        let backing_value = self.tree_iter.next();

        // Prioritise the value from the update map.
        // self.updates.get_mut().get(index).or(backing_value)
        backing_value
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, T: Value> ExactSizeIterator for InterfaceIter<'a, T> {}

#[derive(Debug)]
pub struct InterfaceIterCow<'a, T: Value, U: UpdateMap<T>> {
    pub(crate) tree_iter: Iter<'a, T>,
    pub(crate) updates: &'a mut U,
    pub(crate) index: usize,
}

impl<'a, T: Value, U: UpdateMap<T>> InterfaceIterCow<'a, T, U> {
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
