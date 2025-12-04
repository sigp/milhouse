use crate::cow::{BTreeCow, Cow, VecCow};
use crate::utils::max_btree_index;
use std::collections::{BTreeMap, btree_map::Entry};
use std::ops::ControlFlow;
use triomphe::Arc;
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

    fn get_arc(&self, k: usize) -> Option<Arc<T>>;

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

    fn get_arc(&self, k: usize) -> Option<Arc<T>> {
        self.get(&k).cloned().map(Arc::new)
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

    fn get_arc(&self, k: usize) -> Option<Arc<T>> {
        self.get(k).cloned().map(Arc::new)
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

#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(
    feature = "arbitrary",
    derive(arbitrary::Arbitrary),
    arbitrary(bound = "M: Default")
)]
pub struct MaxMap<M> {
    #[cfg_attr(feature = "arbitrary", arbitrary(default))]
    inner: M,
    max_key: usize,
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
        self.inner.get_mut_with(k, f)
    }

    fn get_cow_with<'a, F>(&'a mut self, k: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
        T: Clone + 'a,
    {
        self.inner.get_cow_with(k, f)
    }

    fn get_arc(&self, k: usize) -> Option<Arc<T>> {
        self.inner.get_arc(k)
    }

    fn insert(&mut self, k: usize, value: T) -> Option<T> {
        if k > self.max_key {
            self.max_key = k;
        }
        self.inner.insert(k, value)
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
        Some(self.max_key).filter(|_| !self.inner.is_empty())
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct ArcMap<M>(pub M);

impl<T, M> UpdateMap<T> for ArcMap<M>
where
    M: UpdateMap<Arc<T>>,
    T: Clone + 'static,
{
    fn get(&self, k: usize) -> Option<&T> {
        self.0.get(k).map(|arc| &**arc)
    }

    fn get_mut_with<F>(&mut self, k: usize, f: F) -> Option<&mut T>
    where
        F: FnOnce(usize) -> Option<T>,
    {
        let value = self.0.get_mut_with(k, |idx| f(idx).map(Arc::new))?;
        Arc::get_mut(value)
    }

    fn get_cow_with<'a, F>(&'a mut self, idx: usize, f: F) -> Option<Cow<'a, T>>
    where
        F: FnOnce(usize) -> Option<&'a T>,
        T: Clone + 'a,
    {
        let arc = self
            .0
            .get_mut_with(idx, |_| Some(Arc::new(f(idx)?.clone())))?;
        let value_mut = Arc::get_mut(arc)?;

        Some(Cow::BTree(BTreeCow::Mutable { value: value_mut }))
    }

    fn get_arc(&self, k: usize) -> Option<Arc<T>> {
        self.0.get(k).cloned()
    }

    fn insert(&mut self, k: usize, value: T) -> Option<T> {
        self.0
            .insert(k, Arc::new(value))
            .and_then(|arc| Arc::try_unwrap(arc).ok())
    }

    fn for_each_range<F, E>(&self, start: usize, end: usize, mut f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>,
    {
        self.0.for_each_range(start, end, |k, v| f(k, &**v))
    }

    fn max_index(&self) -> Option<usize> {
        self.0.max_index()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}
