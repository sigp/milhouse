use crate::cow::{BTreeCow, Cow, VecCow};
use crate::utils::max_btree_index;
use parking_lot::RwLock;
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
        Some(Cow::Vec(cow))
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

#[derive(Debug)]
#[cfg_attr(
    feature = "arbitrary",
    derive(arbitrary::Arbitrary),
    arbitrary(bound = "M: Default")
)]
pub struct MaxMap<M> {
    #[cfg_attr(feature = "arbitrary", arbitrary(default))]
    inner: M,
    max_key: usize,
    #[cfg_attr(feature = "arbitrary", arbitrary(default))]
    range_cache: RwLock<Option<Vec<usize>>>,
}

impl<M: Default> Default for MaxMap<M> {
    fn default() -> Self {
        Self {
            inner: M::default(),
            max_key: 0,
            range_cache: RwLock::new(None),
        }
    }
}

impl<M: Clone> Clone for MaxMap<M> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            max_key: self.max_key,
            // The cache is derived state, so clear it on clone.
            range_cache: RwLock::new(None),
        }
    }
}

impl<M: PartialEq> PartialEq for MaxMap<M> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner && self.max_key == other.max_key
    }
}

impl<M> MaxMap<M> {
    fn invalidate_range_cache(&self) {
        self.range_cache.write().take();
    }
}

impl<M> MaxMap<M> {
    fn rebuild_range_cache<T>(&self)
    where
        M: UpdateMap<T>,
    {
        let Some(max_index) = self.inner.max_index() else {
            self.range_cache.write().replace(Vec::new());
            return;
        };

        let mut keys = Vec::with_capacity(self.inner.len());
        self.inner
            .for_each_range(0, max_index.saturating_add(1), |index, _| {
                keys.push(index);
                ControlFlow::Continue(Ok::<(), ()>(()))
            })
            .expect("collecting range cache cannot fail");

        self.range_cache.write().replace(keys);
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
        let exists = self.inner.get(k).is_some();
        self.invalidate_range_cache();
        let result = self.inner.get_mut_with(k, f);
        if result.is_some() && !exists && k > self.max_key {
            self.max_key = k;
        }
        result
    }

    fn get_cow_with<'a, F>(&'a mut self, k: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
        T: Clone + 'a,
    {
        self.invalidate_range_cache();
        self.inner.get_cow_with(k, f)
    }

    fn insert(&mut self, k: usize, value: T) -> Option<T> {
        self.invalidate_range_cache();
        if k > self.max_key {
            self.max_key = k;
        }
        self.inner.insert(k, value)
    }

    fn for_each_range<F, E>(&self, start: usize, end: usize, f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>,
    {
        if start >= end {
            return Ok(());
        }

        if self.range_cache.read().is_none() {
            self.rebuild_range_cache();
        }

        let cache = self.range_cache.read();
        let keys = cache.as_ref().expect("range cache must be initialized");
        let start_idx = keys.partition_point(|key| *key < start);
        let mut f = f;

        for key in &keys[start_idx..] {
            if *key >= end {
                break;
            }
            if let Some(value) = self.inner.get(*key) {
                match f(*key, value) {
                    ControlFlow::Continue(res) => res?,
                    ControlFlow::Break(()) => break,
                }
            }
        }
        Ok(())
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn max_index(&self) -> Option<usize> {
        self.inner
            .max_index()
            .map(|inner_max| inner_max.max(self.max_key))
    }
}

#[cfg(test)]
mod test {
    use super::{MaxMap, UpdateMap};
    use std::ops::ControlFlow;
    use vec_map::VecMap;

    #[test]
    fn get_mut_with_updates_max_index_for_new_entries() {
        let mut updates = MaxMap::<VecMap<u64>>::default();

        *updates.get_mut_with(5, |index| Some(index as u64)).unwrap() = 42;

        assert_eq!(updates.max_index(), Some(5));
    }

    #[test]
    fn get_cow_with_only_caches_materialized_entries() {
        let mut updates = MaxMap::<VecMap<u64>>::default();
        let backing = 11_u64;

        let _ = updates.get_cow_with(3, |_| Some(&backing)).unwrap();
        assert_eq!(updates.max_index(), None);

        let mut seen = Vec::new();
        updates
            .for_each_range(0, 4, |index, value| {
                seen.push((index, *value));
                ControlFlow::Continue(Ok::<(), ()>(()))
            })
            .unwrap();
        assert!(seen.is_empty());

        let cow = updates.get_cow_with(3, |_| Some(&backing)).unwrap();
        *cow.into_mut().unwrap() = 99;
        assert_eq!(updates.max_index(), Some(3));

        updates
            .for_each_range(0, 4, |index, value| {
                seen.push((index, *value));
                ControlFlow::Continue(Ok::<(), ()>(()))
            })
            .unwrap();
        assert_eq!(seen, vec![(3, 99)]);
    }
}
