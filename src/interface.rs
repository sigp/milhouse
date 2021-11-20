use crate::Error;
use std::collections::{btree_map::Entry, BTreeMap};

pub trait ImmList<T> {
    fn get(&self, idx: usize) -> Option<&T>;

    fn len(&self) -> usize;
}

pub trait MutList<T>: ImmList<T>
where
    T: Clone,
{
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error>;
}

pub trait PushList<T>: MutList<T>
where
    T: Clone,
{
    fn push(&mut self, value: T) -> Result<(), Error>;
}

pub struct Interface<T, B>
where
    T: Clone,
    B: MutList<T>,
{
    backing: B,
    updates: BTreeMap<usize, T>,
}

impl<T, B> Interface<T, B>
where
    T: Clone,
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

    pub fn apply(&mut self) -> Result<(), Error> {
        for (k, v) in self.updates.split_off(&0) {
            self.backing.replace(k, v)?;
        }
        Ok(())
    }
}

impl<T, B> Interface<T, B>
where
    T: Clone,
    B: PushList<T>,
{
    pub fn push(&mut self, value: T) -> Result<(), Error> {
        // Flush changes and push directly (possibly not the most efficient?)
        self.apply()?;
        self.backing.push(value)
    }
}

impl<T, B> Drop for Interface<T, B>
where
    T: Clone,
    B: MutList<T>,
{
    fn drop(&mut self) {
        self.apply().unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::List;
    use typenum::U8;

    #[test]
    fn basic_mutation() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3, 4]).unwrap();
        let mut list_mut = list.as_mut();

        let x = list_mut.get_mut(0).unwrap();
        assert_eq!(*x, 1);
        *x = 11;

        let y = list_mut.get_mut(0).unwrap();
        assert_eq!(*y, 11);

        // Dropping the interface should persist the changes.
        drop(list_mut);
        assert_eq!(*list.get(0).unwrap(), 11);
    }
}
