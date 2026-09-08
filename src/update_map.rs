use crate::cow::{BTreeCow, Cow, CowOnMut, VecCow};
use crate::utils::max_btree_index;
use std::collections::{BTreeMap, btree_map::Entry};
use std::ops::ControlFlow;
use vec_map::VecMap;

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

    /// Return the largest index currently stored in the map.
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
                BTreeCow::Immutable {
                    value,
                    entry: Some(entry),
                }
            }
            Entry::Occupied(entry) => BTreeCow::Mutable {
                value: entry.into_mut(),
            },
        };
        Some(Cow::BTree(cow, CowOnMut::default()))
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

impl<T: Clone> UpdateMap<T> for VecMap<T> {
    fn get(&self, k: usize) -> Option<&T> {
        VecMap::get(self, k)
    }

    fn get_mut_with<F>(&mut self, idx: usize, f: F) -> Option<&mut T>
    where
        F: FnOnce(usize) -> Option<T>,
    {
        match self.entry(idx) {
            vec_map::Entry::Vacant(entry) => {
                // Copy on write.
                let value = f(idx)?;
                Some(entry.insert(value))
            }
            vec_map::Entry::Occupied(entry) => Some(entry.into_mut()),
        }
    }

    fn get_cow_with<'a, F>(&'a mut self, idx: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
    {
        let cow = match self.entry(idx) {
            vec_map::Entry::Vacant(entry) => {
                let value = f(idx)?;
                VecCow::Immutable {
                    value,
                    entry: Some(entry),
                }
            }
            vec_map::Entry::Occupied(entry) => VecCow::Mutable {
                value: entry.into_mut(),
            },
        };
        Some(Cow::Vec(cow, CowOnMut::default()))
    }

    fn insert(&mut self, idx: usize, value: T) -> Option<T> {
        VecMap::insert(self, idx, value)
    }

    fn for_each_range<F, E>(&self, start: usize, end: usize, mut f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>,
    {
        for key in start..end {
            if key >= self.capacity() {
                break;
            }
            if let Some(value) = self.get(key) {
                match f(key, value) {
                    ControlFlow::Continue(res) => res?,
                    ControlFlow::Break(()) => break,
                }
            }
        }
        Ok(())
    }

    fn max_index(&self) -> Option<usize> {
        self.keys().next_back()
    }

    fn len(&self) -> usize {
        VecMap::len(self)
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MaxIndexState {
    /// The inner map is known to be empty.
    #[default]
    Empty,
    /// The largest index in the inner map is known exactly.
    Known(usize),
}

impl MaxIndexState {
    pub(crate) fn record_insert(&mut self, index: usize) {
        match self {
            Self::Empty => *self = Self::Known(index),
            Self::Known(max_index) => *max_index = (*max_index).max(index),
        }
    }
}

#[derive(Debug, Default, Clone)]
#[cfg_attr(
    feature = "arbitrary",
    derive(arbitrary::Arbitrary),
    arbitrary(bound = "M: Default")
)]
pub struct MaxMap<M> {
    #[cfg_attr(feature = "arbitrary", arbitrary(default))]
    inner: M,
    #[cfg_attr(feature = "arbitrary", arbitrary(default))]
    max_index: MaxIndexState,
}

impl<M: PartialEq> PartialEq for MaxMap<M> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<T, M> UpdateMap<T> for MaxMap<M>
where
    M: UpdateMap<T>,
{
    fn get(&self, k: usize) -> Option<&T> {
        self.inner.get(k)
    }

    fn get_mut_with<F>(&mut self, k: usize, f: F) -> Option<&mut T>
    where
        F: FnOnce(usize) -> Option<T>,
    {
        let value = self.inner.get_mut_with(k, f)?;
        self.max_index.record_insert(k);
        Some(value)
    }

    fn get_cow_with<'a, F>(&'a mut self, k: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
        T: Clone + 'a,
    {
        let Self { inner, max_index } = self;
        let cow = inner.get_cow_with(k, f)?;

        Some(cow.with_max_index(max_index, k))
    }

    fn insert(&mut self, k: usize, value: T) -> Option<T> {
        let previous = self.inner.insert(k, value);
        self.max_index.record_insert(k);
        previous
    }

    fn for_each_range<F, E>(&self, start: usize, end: usize, f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>,
    {
        self.inner.for_each_range(start, end, f)
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn max_index(&self) -> Option<usize> {
        match self.max_index {
            MaxIndexState::Empty => None,
            MaxIndexState::Known(max_index) => Some(max_index),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{MaxIndexState, MaxMap, UpdateMap};
    use std::collections::BTreeMap;
    use vec_map::VecMap;

    type TestMap = MaxMap<VecMap<u64>>;
    type TestBTreeMap = MaxMap<BTreeMap<usize, u64>>;

    #[test]
    fn max_map_defaults_to_empty() {
        let map = TestMap::default();

        assert_eq!(map.max_index, MaxIndexState::Empty);
        assert_eq!(map.max_index(), None);
    }

    #[test]
    fn max_map_tracks_get_mut_with_insertions() {
        let mut map = TestMap::default();

        assert!(map.get_mut_with(3, |_| Some(30)).is_some());
        assert_eq!(map.max_index, MaxIndexState::Known(3));
        assert_eq!(map.max_index(), Some(3));

        assert!(map.get_mut_with(17, |_| Some(170)).is_some());
        assert_eq!(map.max_index, MaxIndexState::Known(17));
        assert_eq!(map.max_index(), Some(17));

        assert!(map.get_mut_with(23, |_| None).is_none());
        assert_eq!(map.max_index, MaxIndexState::Known(17));
        assert_eq!(map.max_index(), Some(17));
    }

    #[test]
    fn max_map_tracks_cow_into_mut_insertions() {
        let mut map = TestMap::default();
        map.insert(3, 30);
        let backing_value = 170;

        let cow = map
            .get_cow_with(17, |_| Some(&backing_value))
            .expect("backing value should produce a Cow");
        *cow.into_mut().expect("Cow should have a vacant entry") = 171;

        assert_eq!(map.max_index, MaxIndexState::Known(17));
        assert_eq!(map.max_index(), Some(17));
    }

    #[test]
    fn max_map_tracks_btree_cow_insertions() {
        let mut map = TestBTreeMap::default();
        map.insert(3, 30);
        let backing_value = 170;

        let cow = map
            .get_cow_with(17, |_| Some(&backing_value))
            .expect("backing value should produce a Cow");
        *cow.into_mut().expect("Cow should have a vacant entry") = 171;

        assert_eq!(map.max_index, MaxIndexState::Known(17));
        assert_eq!(map.max_index(), Some(17));
    }

    #[test]
    fn max_map_tracks_cow_make_mut_insertions() {
        let mut map = TestMap::default();
        map.insert(3, 30);
        let backing_value = 170;

        let mut cow = map
            .get_cow_with(17, |_| Some(&backing_value))
            .expect("backing value should produce a Cow");
        *cow.make_mut().expect("Cow should have a vacant entry") = 171;

        assert_eq!(map.max_index, MaxIndexState::Known(17));
        assert_eq!(map.max_index(), Some(17));
    }

    #[test]
    fn max_map_ignores_read_only_cow_access() {
        let mut map = TestMap::default();
        map.insert(3, 30);
        let expected = map.clone();
        let backing_value = 170;

        let cow = map
            .get_cow_with(17, |_| Some(&backing_value))
            .expect("backing value should produce a Cow");
        assert_eq!(*cow, backing_value);

        assert_eq!(map.max_index, MaxIndexState::Known(3));
        assert_eq!(map.max_index(), Some(3));
        assert_eq!(map, expected);
    }

    #[test]
    fn max_map_tracks_mutation_of_existing_entry() {
        let mut map = TestMap::default();
        map.insert(3, 30);

        let mut cow = map
            .get_cow_with(3, |_| None)
            .expect("existing entry should produce a Cow");
        *cow.make_mut().expect("existing entry should be mutable") = 31;

        assert_eq!(map.max_index, MaxIndexState::Known(3));
        assert_eq!(map.max_index(), Some(3));
        assert_eq!(map.get(3), Some(&31));
    }

    #[test]
    fn max_map_insert_preserves_cow_maximum() {
        let mut map = TestMap::default();
        map.insert(3, 30);
        let backing_value = 170;

        let cow = map
            .get_cow_with(17, |_| Some(&backing_value))
            .expect("backing value should produce a Cow");
        *cow.into_mut().expect("Cow should have a vacant entry") = 171;
        map.insert(10, 100);

        assert_eq!(map.max_index, MaxIndexState::Known(17));
        assert_eq!(map.max_index(), Some(17));
    }
}
