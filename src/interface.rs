use crate::cow::Cow;
use crate::{interface_iter::InterfaceIter, iter::Iter, Error};
use std::collections::{btree_map::Entry, BTreeMap};
use tree_hash::TreeHash;

pub trait ImmList<T>
where
    T: TreeHash + Clone,
{
    fn get(&self, idx: usize) -> Option<&T>;

    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn iter_from(&self, index: usize) -> Iter<T>;
}

pub trait MutList<T>: ImmList<T>
where
    T: TreeHash + Clone,
{
    fn validate_push(&self) -> Result<(), Error>;
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error>;
}

#[derive(Debug, PartialEq, Clone)]
pub struct Interface<T, B>
where
    T: TreeHash + Clone,
    B: MutList<T>,
{
    pub(crate) backing: B,
    pub(crate) updates: BTreeMap<usize, T>,
}

impl<T, B> Interface<T, B>
where
    T: TreeHash + Clone,
    B: MutList<T>,
{
    pub fn new(backing: B) -> Self {
        Self {
            backing,
            updates: BTreeMap::new(),
        }
    }

    pub fn get(&self, idx: usize) -> Option<&T> {
        self.updates.get(&idx).or_else(|| self.backing.get(idx))
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        match self.updates.entry(idx) {
            Entry::Vacant(entry) => {
                // Copy on write.
                let value = self.backing.get(idx)?.clone();
                Some(entry.insert(value))
            }
            Entry::Occupied(entry) => Some(entry.into_mut()),
        }
    }

    pub fn get_cow<'a>(&'a mut self, index: usize) -> Option<Cow<'a, T>> {
        // FIXME(sproul): trick the borrow checker without having to do a double look-up
        match self.updates.contains_key(&index) {
            true => {
                let value = self.updates.get_mut(&index)?;
                Some(Cow::Mutable { value })
            }
            false => {
                let value = self.backing.get(index)?;
                Some(Cow::Immutable {
                    value,
                    index,
                    updates: &mut self.updates,
                })
            }
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        self.backing.validate_push()?;

        let index = self.len();
        self.updates.insert(index, value);

        Ok(())
    }

    pub fn apply_updates(&mut self) -> Result<(), Error> {
        for (k, v) in self.updates.split_off(&0) {
            self.backing.replace(k, v)?;
        }
        Ok(())
    }

    pub fn has_pending_updates(&self) -> bool {
        !self.updates.is_empty()
    }

    pub fn iter(&self) -> InterfaceIter<T> {
        self.iter_from(0)
    }

    pub fn iter_from(&self, index: usize) -> InterfaceIter<T> {
        InterfaceIter {
            tree_iter: self.backing.iter_from(index),
            updates: &self.updates,
            index,
            length: self.len(),
        }
    }

    /// Compute the maximum index of the cached updates.
    fn max_update_index(&self) -> Option<usize> {
        self.updates.keys().next_back().copied()
    }

    pub fn len(&self) -> usize {
        let backing_len = self.backing.len();
        self.max_update_index().map_or(backing_len, |max_idx| {
            std::cmp::max(max_idx + 1, backing_len)
        })
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod test {
    use crate::List;
    use typenum::U8;

    #[test]
    fn basic_mutation() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3, 4]).unwrap();

        let x = list.get_mut(0).unwrap();
        assert_eq!(*x, 1);
        *x = 11;

        let y = list.get_mut(0).unwrap();
        assert_eq!(*y, 11);

        // Applying the changes should persist them.
        assert!(list.has_pending_updates());
        list.apply_updates().unwrap();
        assert!(!list.has_pending_updates());

        assert_eq!(*list.get(0).unwrap(), 11);
    }

    #[test]
    fn cow_mutate_twice() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3]).unwrap();

        let c1 = list.get_cow(0).unwrap();
        assert_eq!(*c1, 1);
        *c1.to_mut() = 10;

        assert_eq!(*list.get(0).unwrap(), 10);

        let c2 = list.get_cow(0).unwrap();
        assert_eq!(*c2, 10);
        *c2.to_mut() = 11;
        assert_eq!(*list.get(0).unwrap(), 11);

        assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec![11, 2, 3]);
    }
}
