use crate::level_iter::LevelIter;
use crate::update_map::UpdateMap;
use crate::utils::{arb_arc_swap, partial_eq_arc_swap, updated_length, Length};
use crate::{
    interface_iter::{InterfaceIter, InterfaceIterCow},
    iter::Iter,
    Cow, Error, Tree, Value, ValueRef,
};
use arbitrary::Arbitrary;
use arc_swap::ArcSwap;
use derivative::Derivative;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::sync::Arc;
use tree_hash::Hash256;

pub type GetResult<'a, T> = arc_swap::access::MapGuard<
    &'a ArcSwap<Arc<T>>,
    (),
    fn(&'a Arc<Tree<T>>, usize, usize, usize) -> &'a T,
    &'a T,
>;

pub trait ImmList<T: Value> {
    fn get(&self, idx: usize) -> Option<GetResult<T>>;

    fn len(&self) -> Length;

    fn is_empty(&self) -> bool {
        self.len().as_usize() == 0
    }

    fn iter_from(&self, index: usize) -> Iter<T>;

    fn level_iter_from(&self, index: usize) -> LevelIter<T>;
}

pub trait MutList<T: Value>: ImmList<T> {
    fn validate_push(current_len: usize) -> Result<(), Error>;
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error>;
    fn update<U: UpdateMap<T>>(
        &self,
        updates: U,
        hash_updates: Option<BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<(), Error>;
}

#[derive(Debug, Derivative, Arbitrary)]
#[derivative(PartialEq)]
pub struct Interface<T, B, U>
where
    T: Value,
    B: MutList<T>,
    U: UpdateMap<T>,
{
    pub(crate) backing: B,
    #[derivative(PartialEq(compare_with = "partial_eq_arc_swap"))]
    #[arbitrary(with = arb_arc_swap)]
    pub(crate) updates: ArcSwap<Arc<U>>,
    pub(crate) _phantom: PhantomData<T>,
}

impl<T, B, U> Clone for Interface<T, B, U>
where
    T: Value,
    B: MutList<T> + Clone,
    U: UpdateMap<T>,
{
    fn clone(&self) -> Self {
        Self {
            backing: self.backing.clone(),
            updates: ArcSwap::new(self.updates.load_full()),
            _phantom: PhantomData,
        }
    }
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
            updates: ArcSwap::new(U::default()),
            _phantom: PhantomData,
        }
    }

    pub fn get(&self, idx: usize) -> Option<GetResult<T>> {
        panic!()

        // let values_in_updates = ArcSwap::map(&self.updates, || )
        /*
        RwLockReadGuard::try_map(self.updates.read(), |updates| updates.get(idx))
            .ok()
            .map(ValueRef::Pending)
            .or_else(|| self.backing.get(idx).map(ValueRef::Applied))
        */
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        self.updates
            .get_mut()
            .get_mut_with(idx, |idx| self.backing.get(idx).cloned())
    }

    pub fn get_cow(&mut self, index: usize) -> Option<Cow<T>> {
        self.updates
            .get_mut()
            .get_cow_with(index, |idx| self.backing.get(idx))
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        let index = self.len();
        B::validate_push(index)?;
        self.updates.get_mut().insert(index, value);

        Ok(())
    }

    pub fn apply_updates(&self) -> Result<(), Error> {
        let mut updates = self.updates.write();
        if !updates.is_empty() {
            self.backing.update(std::mem::take(&mut *updates), None)?;
            drop(updates);
            Ok(())
        } else {
            Ok(())
        }
    }

    pub fn has_pending_updates(&self) -> bool {
        !self.updates.read().is_empty()
    }

    pub fn iter(&self) -> InterfaceIter<T> {
        self.iter_from(0)
    }

    pub fn iter_from(&self, index: usize) -> InterfaceIter<T> {
        InterfaceIter {
            tree_iter: self.backing.iter_from(index),
            index,
            length: self.len(),
        }
    }

    pub fn iter_cow(&mut self) -> InterfaceIterCow<T, U> {
        let index = 0;
        InterfaceIterCow {
            tree_iter: self.backing.iter_from(index),
            updates: self.updates.get_mut(),
            index,
        }
    }

    pub fn level_iter_from(&self, index: usize) -> Result<LevelIter<T>, Error> {
        if self.has_pending_updates() {
            Err(Error::LevelIterPendingUpdates)
        } else {
            Ok(self.backing.level_iter_from(index))
        }
    }

    pub fn len(&self) -> usize {
        updated_length(self.backing.len(), &*self.updates.read()).as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn bulk_update(&mut self, updates: U) -> Result<(), Error> {
        let self_updates = self.updates.get_mut();
        if !self_updates.is_empty() {
            return Err(Error::BulkUpdateUnclean);
        }
        *self_updates = updates;
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
}
