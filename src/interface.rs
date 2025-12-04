use crate::level_iter::LevelIter;
use crate::update_map::UpdateMap;
use crate::utils::{Length, updated_length};
use crate::{
    Cow, Error, Value,
    interface_iter::{InterfaceIter, InterfaceIterCow},
    iter::Iter,
};
use std::collections::BTreeMap;
use std::marker::PhantomData;
use tree_hash::Hash256;

pub trait ImmList<T: Value> {
    fn get(&self, idx: usize) -> Option<&T>;

    fn len(&self) -> Length;

    fn is_empty(&self) -> bool {
        self.len().as_usize() == 0
    }

    fn iter_from(&self, index: usize) -> Iter<'_, T>;

    fn level_iter_from(&self, index: usize) -> LevelIter<'_, T>;
}

pub trait MutList<T: Value>: ImmList<T> {
    fn validate_push(current_len: usize) -> Result<(), Error>;
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error>;
    fn update<U: UpdateMap<T>>(
        &mut self,
        updates: U,
        hash_updates: Option<BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<(), Error>;
}

#[derive(Debug, PartialEq, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Interface<T, B, U>
where
    T: Value,
    B: MutList<T>,
    U: UpdateMap<T>,
{
    pub(crate) backing: B,
    pub(crate) updates: U,
    pub(crate) _phantom: PhantomData<T>,
}

impl<T, B, U> Interface<T, B, U>
where
    T: Value,
    B: MutList<T>,
    U: UpdateMap<T>,
{
    pub fn new(backing: B) -> Self {
        Self {
            backing,
            updates: U::default(),
            _phantom: PhantomData,
        }
    }

    pub fn get(&self, idx: usize) -> Option<&T> {
        self.updates.get(idx).or_else(|| self.backing.get(idx))
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        self.updates
            .get_mut_with(idx, |idx| self.backing.get(idx).cloned())
    }

    pub fn get_cow(&mut self, index: usize) -> Option<Cow<'_, T>> {
        self.updates
            .get_cow_with(index, |idx| self.backing.get(idx))
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        let index = self.len();
        B::validate_push(index)?;
        self.updates.insert(index, value);

        Ok(())
    }

    pub fn apply_updates(&mut self) -> Result<(), Error> {
        if !self.updates.is_empty() {
            let updates = std::mem::take(&mut self.updates);
            self.backing.update(updates, None)
        } else {
            Ok(())
        }
    }

    pub fn has_pending_updates(&self) -> bool {
        !self.updates.is_empty()
    }

    pub fn iter(&self) -> InterfaceIter<'_, T, U> {
        self.iter_from(0)
    }

    pub fn iter_from(&self, index: usize) -> InterfaceIter<'_, T, U> {
        InterfaceIter {
            tree_iter: self.backing.iter_from(index),
            updates: &self.updates,
            index,
            length: self.len(),
        }
    }

    pub fn iter_cow(&mut self) -> InterfaceIterCow<'_, T, U> {
        self.iter_cow_from(0)
    }

    pub fn iter_cow_from(&mut self, index: usize) -> InterfaceIterCow<'_, T, U> {
        InterfaceIterCow {
            tree_iter: self.backing.iter_from(index),
            updates: &mut self.updates,
            index,
        }
    }

    pub fn level_iter_from(&self, index: usize) -> Result<LevelIter<'_, T>, Error> {
        if self.has_pending_updates() {
            Err(Error::LevelIterPendingUpdates)
        } else {
            Ok(self.backing.level_iter_from(index))
        }
    }

    pub fn len(&self) -> usize {
        updated_length(self.backing.len(), &self.updates).as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn bulk_update(&mut self, updates: U) -> Result<(), Error> {
        if !self.updates.is_empty() {
            return Err(Error::BulkUpdateUnclean);
        }
        self.updates = updates;
        Ok(())
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

        // Apply empty updates should be OK.
        list.apply_updates().unwrap();

        assert_eq!(*list.get(0).unwrap(), 11);
    }

    #[test]
    fn cow_mutate_twice() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3]).unwrap();

        let c1 = list.get_cow(0).unwrap();
        assert_eq!(*c1, 1);
        *c1.into_mut().unwrap() = 10;

        assert_eq!(*list.get(0).unwrap(), 10);

        let c2 = list.get_cow(0).unwrap();
        assert_eq!(*c2, 10);
        *c2.into_mut().unwrap() = 11;
        assert_eq!(*list.get(0).unwrap(), 11);

        assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec![11, 2, 3]);
    }

    #[test]
    fn cow_iter() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3]).unwrap();

        let mut iter = list.iter_cow();
        while let Some((index, v)) = iter.next_cow() {
            *v.into_mut().unwrap() = index as u64;
        }

        assert_eq!(list.to_vec(), vec![0, 1, 2]);
    }

    #[test]
    fn cow_iter_from() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3, 4, 5]).unwrap();

        let mut iter = list.iter_cow_from(2).unwrap();
        while let Some((index, v)) = iter.next_cow() {
            *v.into_mut().unwrap() = (index * 10) as u64;
        }

        assert_eq!(list.to_vec(), vec![1, 2, 20, 30, 40]);
    }
}
