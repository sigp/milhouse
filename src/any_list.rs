//! View types that abstract over `List` and `ProgressiveList`.
//!
//! These are intended for downstream consumers (like Lighthouse's `BeaconState`) where the
//! same field is stored as a `List` in some variants and a `ProgressiveList` in others.

use crate::interface_iter::{InterfaceIter, InterfaceIterCow};
use crate::progressive_list::{ProgressiveListIter, ProgressiveListIterCow};
use crate::update_map::MaxMap;
use crate::{Cow, Error, List, ProgressiveList, UpdateMap, Value};
use serde::{Serialize, Serializer};
use typenum::Unsigned;
use vec_map::VecMap;

/// Immutable view over either a fixed-capacity `List` or a `ProgressiveList`.
///
/// Methods take `self` by value (the view is `Copy`) and return data tied to the underlying
/// borrow `'a`, so views can be used as temporaries, e.g. `state.validators().iter()`.
#[derive(Debug)]
pub enum AnyListRef<'a, T: Value, N: Unsigned, U: UpdateMap<T> = MaxMap<VecMap<T>>> {
    Basic(&'a List<T, N, U>),
    Progressive(&'a ProgressiveList<T, U>),
}

// Manual `Clone`/`Copy` impls to avoid spurious `T: Copy` bounds from the derive.
impl<T: Value, N: Unsigned, U: UpdateMap<T>> Clone for AnyListRef<'_, T, N, U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> Copy for AnyListRef<'_, T, N, U> {}

impl<'a, T: Value, N: Unsigned, U: UpdateMap<T>> AnyListRef<'a, T, N, U> {
    pub fn len(self) -> usize {
        match self {
            Self::Basic(list) => list.len(),
            Self::Progressive(list) => list.len(),
        }
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub fn get(self, index: usize) -> Option<&'a T> {
        match self {
            Self::Basic(list) => list.get(index),
            Self::Progressive(list) => list.get(index),
        }
    }

    pub fn iter(self) -> AnyListIter<'a, T, U> {
        match self {
            Self::Basic(list) => AnyListIter::Basic(list.iter()),
            Self::Progressive(list) => AnyListIter::Progressive(list.iter()),
        }
    }

    pub fn iter_from(self, index: usize) -> Result<AnyListIter<'a, T, U>, Error> {
        match self {
            Self::Basic(list) => list.iter_from(index).map(AnyListIter::Basic),
            Self::Progressive(list) => list.iter_from(index).map(AnyListIter::Progressive),
        }
    }

    pub fn has_pending_updates(self) -> bool {
        match self {
            Self::Basic(list) => list.has_pending_updates(),
            Self::Progressive(list) => list.has_pending_updates(),
        }
    }

    pub fn to_vec(self) -> Vec<T> {
        match self {
            Self::Basic(list) => list.to_vec(),
            Self::Progressive(list) => list.to_vec(),
        }
    }

    /// Clone the underlying list into an owned `AnyList`.
    pub fn to_owned_list(self) -> AnyList<T, N, U> {
        match self {
            Self::Basic(list) => AnyList::Basic(list.clone()),
            Self::Progressive(list) => AnyList::Progressive(list.clone()),
        }
    }

    /// Compute the tree hash root of the underlying list.
    ///
    /// NOTE: like `List`/`ProgressiveList`, this is only valid once pending updates have been
    /// applied.
    pub fn tree_hash_root(self) -> tree_hash::Hash256
    where
        T: Send + Sync,
    {
        use tree_hash::TreeHash;
        match self {
            Self::Basic(list) => list.tree_hash_root(),
            Self::Progressive(list) => list.tree_hash_root(),
        }
    }
}

impl<T: Value + Serialize, N: Unsigned, U: UpdateMap<T>> Serialize for AnyListRef<'_, T, N, U> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Self::Basic(list) => list.serialize(serializer),
            Self::Progressive(list) => list.serialize(serializer),
        }
    }
}

impl<'a, T: Value, N: Unsigned, U: UpdateMap<T>> IntoIterator for AnyListRef<'a, T, N, U> {
    type Item = &'a T;
    type IntoIter = AnyListIter<'a, T, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Mutable view over either a fixed-capacity `List` or a `ProgressiveList`.
#[derive(Debug)]
pub enum AnyListMut<'a, T: Value, N: Unsigned, U: UpdateMap<T> = MaxMap<VecMap<T>>> {
    Basic(&'a mut List<T, N, U>),
    Progressive(&'a mut ProgressiveList<T, U>),
}

impl<'a, T: Value, N: Unsigned, U: UpdateMap<T>> AnyListMut<'a, T, N, U> {
    pub fn as_ref(&self) -> AnyListRef<'_, T, N, U> {
        match self {
            Self::Basic(list) => AnyListRef::Basic(list),
            Self::Progressive(list) => AnyListRef::Progressive(list),
        }
    }

    pub fn len(&self) -> usize {
        self.as_ref().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.as_ref().get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        match self {
            Self::Basic(list) => list.get_mut(index),
            Self::Progressive(list) => list.get_mut(index),
        }
    }

    pub fn get_cow(&mut self, index: usize) -> Option<Cow<'_, T>> {
        match self {
            Self::Basic(list) => list.get_cow(index),
            Self::Progressive(list) => list.get_cow(index),
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        match self {
            Self::Basic(list) => list.push(value),
            Self::Progressive(list) => list.push(value),
        }
    }

    pub fn apply_updates(&mut self) -> Result<(), Error> {
        match self {
            Self::Basic(list) => list.apply_updates(),
            Self::Progressive(list) => list.apply_updates(),
        }
    }

    pub fn has_pending_updates(&self) -> bool {
        self.as_ref().has_pending_updates()
    }

    pub fn pop_front(&mut self, n: usize) -> Result<(), Error> {
        match self {
            Self::Basic(list) => list.pop_front(n),
            Self::Progressive(list) => list.pop_front(n),
        }
    }

    pub fn iter_cow(&mut self) -> AnyListIterCow<'_, T, U> {
        match self {
            Self::Basic(list) => AnyListIterCow::Basic(list.iter_cow()),
            Self::Progressive(list) => AnyListIterCow::Progressive(list.iter_cow()),
        }
    }

    /// Consume the view and return a mutable reference to the element at `index`.
    pub fn into_get_mut(self, index: usize) -> Option<&'a mut T> {
        match self {
            Self::Basic(list) => list.get_mut(index),
            Self::Progressive(list) => list.get_mut(index),
        }
    }

    /// Consume the view and return a CoW reference to the element at `index`.
    pub fn into_get_cow(self, index: usize) -> Option<Cow<'a, T>> {
        match self {
            Self::Basic(list) => list.get_cow(index),
            Self::Progressive(list) => list.get_cow(index),
        }
    }
}

/// Owned list that is either a fixed-capacity `List` or a `ProgressiveList`.
#[derive(Debug, Clone)]
pub enum AnyList<T: Value, N: Unsigned, U: UpdateMap<T> = MaxMap<VecMap<T>>> {
    Basic(List<T, N, U>),
    Progressive(ProgressiveList<T, U>),
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> AnyList<T, N, U> {
    pub fn as_ref(&self) -> AnyListRef<'_, T, N, U> {
        match self {
            Self::Basic(list) => AnyListRef::Basic(list),
            Self::Progressive(list) => AnyListRef::Progressive(list),
        }
    }

    pub fn as_mut(&mut self) -> AnyListMut<'_, T, N, U> {
        match self {
            Self::Basic(list) => AnyListMut::Basic(list),
            Self::Progressive(list) => AnyListMut::Progressive(list),
        }
    }

    pub fn len(&self) -> usize {
        self.as_ref().len()
    }

    pub fn is_empty(&self) -> bool {
        self.as_ref().is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.as_ref().get(index)
    }

    pub fn iter(&self) -> AnyListIter<'_, T, U> {
        self.as_ref().iter()
    }

    pub fn iter_from(&self, index: usize) -> Result<AnyListIter<'_, T, U>, Error> {
        self.as_ref().iter_from(index)
    }

    pub fn has_pending_updates(&self) -> bool {
        self.as_ref().has_pending_updates()
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.as_ref().to_vec()
    }
}

impl<T: Value + Serialize, N: Unsigned, U: UpdateMap<T>> Serialize for AnyList<T, N, U> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_ref().serialize(serializer)
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> From<List<T, N, U>> for AnyList<T, N, U> {
    fn from(list: List<T, N, U>) -> Self {
        Self::Basic(list)
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> From<ProgressiveList<T, U>> for AnyList<T, N, U> {
    fn from(list: ProgressiveList<T, U>) -> Self {
        Self::Progressive(list)
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T> + PartialEq> PartialEq for AnyList<T, N, U> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Basic(a), Self::Basic(b)) => a == b,
            (Self::Progressive(a), Self::Progressive(b)) => a == b,
            _ => false,
        }
    }
}

/// Iterator over either list type.
#[derive(Debug)]
pub enum AnyListIter<'a, T: Value, U: UpdateMap<T>> {
    Basic(InterfaceIter<'a, T, U>),
    Progressive(ProgressiveListIter<'a, T, U>),
}

impl<'a, T: Value, U: UpdateMap<T>> Iterator for AnyListIter<'a, T, U> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match self {
            Self::Basic(iter) => iter.next(),
            Self::Progressive(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Basic(iter) => iter.size_hint(),
            Self::Progressive(iter) => iter.size_hint(),
        }
    }
}

impl<T: Value, U: UpdateMap<T>> ExactSizeIterator for AnyListIter<'_, T, U> {}

/// Copy-on-write iterator over either list type.
#[derive(Debug)]
pub enum AnyListIterCow<'a, T: Value, U: UpdateMap<T>> {
    Basic(InterfaceIterCow<'a, T, U>),
    Progressive(ProgressiveListIterCow<'a, T, U>),
}

impl<T: Value, U: UpdateMap<T>> AnyListIterCow<'_, T, U> {
    pub fn next_cow(&mut self) -> Option<(usize, Cow<'_, T>)> {
        match self {
            Self::Basic(iter) => iter.next_cow(),
            Self::Progressive(iter) => iter.next_cow(),
        }
    }
}
