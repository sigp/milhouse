use crate::Error;
use crate::update_map::MaxIndexState;
use std::collections::btree_map::VacantEntry;
use std::ops::Deref;

/// State updated when a [`Cow`] is made mutable.
///
/// This is public because it is part of the public `Cow` variants, but its contents are an
/// implementation detail.
#[doc(hidden)]
#[derive(Default)]
pub struct CowOnMut<'a> {
    max_index: Option<(&'a mut MaxIndexState, usize)>,
}

impl CowOnMut<'_> {
    fn run(&mut self) {
        // Update through the borrow before clearing the one-shot action. This
        // avoids a borrowed Option::take, which Aeneas cannot currently model.
        if let Some((max_index, index)) = &mut self.max_index {
            max_index.record_insert(*index);
        }
        self.max_index = None;
    }
}

pub enum Cow<'a, T: Clone> {
    BTree(BTreeCow<'a, T>, CowOnMut<'a>),
    Vec(VecCow<'a, T>, CowOnMut<'a>),
}

impl<T: Clone> Deref for Cow<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::BTree(cow, _) => cow.deref(),
            Self::Vec(cow, _) => cow.deref(),
        }
    }
}

impl<'a, T: Clone> Cow<'a, T> {
    pub fn into_mut(self) -> Result<&'a mut T, Error> {
        // Keep this consuming path separate from the borrowed CowTrait methods.
        // Explicit matches also avoid Aeneas's borrowed Result adapter mismatch.
        match self {
            Self::BTree(inner, mut on_mut) => match inner.into_mut_inner() {
                Ok(value) => {
                    on_mut.run();
                    Ok(value)
                }
                Err(error) => Err(error),
            },
            Self::Vec(inner, mut on_mut) => match inner.into_mut_inner() {
                Ok(value) => {
                    on_mut.run();
                    Ok(value)
                }
                Err(error) => Err(error),
            },
        }
    }

    pub fn make_mut(&mut self) -> Result<&mut T, Error> {
        match self {
            Self::BTree(cow, on_mut) => {
                let value = cow.make_mut()?;
                on_mut.run();
                Ok(value)
            }
            Self::Vec(cow, on_mut) => {
                let value = cow.make_mut()?;
                on_mut.run();
                Ok(value)
            }
        }
    }

    pub(crate) fn with_max_index(mut self, max_index: &'a mut MaxIndexState, index: usize) -> Self {
        match &mut self {
            Self::BTree(_, on_mut) | Self::Vec(_, on_mut) => {
                on_mut.max_index = Some((max_index, index));
            }
        }
        self
    }
}

pub trait CowTrait<'a, T: Clone>: Deref<Target = T> {
    fn into_mut(self) -> Result<&'a mut T, Error>;

    fn make_mut(&mut self) -> Result<&mut T, Error>;
}

pub enum BTreeCow<'a, T: Clone> {
    Immutable {
        value: &'a T,
        entry: Option<VacantEntry<'a, usize, T>>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> BTreeCow<'a, T> {
    // A concrete caller avoids pulling the other borrowed trait methods into extraction.
    #[inline]
    fn into_mut_inner(self) -> Result<&'a mut T, Error> {
        match self {
            Self::Immutable { value, entry } => match entry {
                Some(entry) => Ok(entry.insert(value.clone())),
                None => Err(Error::CowMissingEntry),
            },
            Self::Mutable { value } => Ok(value),
        }
    }
}

impl<'a, T: Clone> CowTrait<'a, T> for BTreeCow<'a, T> {
    fn into_mut(self) -> Result<&'a mut T, Error> {
        self.into_mut_inner()
    }

    fn make_mut(&mut self) -> Result<&mut T, Error> {
        match self {
            Self::Mutable { value } => Ok(value),
            Self::Immutable { entry, value } => {
                let value_mut_ref = entry
                    .take()
                    .ok_or(Error::CowMissingEntry)?
                    .insert(value.clone());
                *self = Self::Mutable {
                    value: value_mut_ref,
                };
                self.make_mut()
            }
        }
    }
}

impl<T: Clone> Deref for BTreeCow<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::Immutable { value, .. } => value,
            Self::Mutable { value } => value,
        }
    }
}

pub enum VecCow<'a, T: Clone> {
    Immutable {
        value: &'a T,
        entry: Option<vec_map::VacantEntry<'a, T>>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> VecCow<'a, T> {
    // A concrete caller avoids pulling the other borrowed trait methods into extraction.
    #[inline]
    fn into_mut_inner(self) -> Result<&'a mut T, Error> {
        match self {
            Self::Immutable { value, entry } => match entry {
                Some(entry) => Ok(entry.insert(value.clone())),
                None => Err(Error::CowMissingEntry),
            },
            Self::Mutable { value } => Ok(value),
        }
    }
}

impl<'a, T: Clone> CowTrait<'a, T> for VecCow<'a, T> {
    fn into_mut(self) -> Result<&'a mut T, Error> {
        self.into_mut_inner()
    }

    fn make_mut(&mut self) -> Result<&mut T, Error> {
        match self {
            Self::Mutable { value } => Ok(value),
            Self::Immutable { entry, value } => {
                let value_mut_ref = entry
                    .take()
                    .ok_or(Error::CowMissingEntry)?
                    .insert(value.clone());
                *self = Self::Mutable {
                    value: value_mut_ref,
                };
                self.make_mut()
            }
        }
    }
}

impl<T: Clone> Deref for VecCow<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::Immutable { value, .. } => value,
            Self::Mutable { value } => value,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BTreeCow, Cow, CowOnMut, VecCow};
    use crate::Error;
    use crate::update_map::{MaxIndexState, MaxMap, UpdateMap};
    use std::cell::Cell;
    use std::collections::BTreeMap;
    use std::rc::Rc;
    use vec_map::VecMap;

    struct CountedClone {
        value: u64,
        calls: Rc<Cell<usize>>,
    }

    impl Clone for CountedClone {
        fn clone(&self) -> Self {
            self.calls.set(self.calls.get() + 1);
            Self {
                value: self.value + 1,
                calls: self.calls.clone(),
            }
        }
    }

    fn consuming_clone_protocol<M: UpdateMap<CountedClone>>() {
        let mut updates = M::default();
        let calls = Rc::new(Cell::new(0));
        let backing = CountedClone {
            value: 16,
            calls: calls.clone(),
        };
        let handle = updates.get_cow_with_value(17, Some(&backing)).unwrap();
        assert_eq!(handle.value, 16);
        assert_eq!(calls.get(), 0);
        let value = handle.into_mut().unwrap();
        // Materialization uses the actual clone result, which need not be identical.
        assert_eq!(value.value, 17);
        value.value = 18;
        assert_eq!(calls.get(), 1);
        assert_eq!(updates.get(17).unwrap().value, 18);
        assert_eq!(updates.max_index(), Some(17));
        assert_eq!(backing.value, 16);

        let value = updates
            .get_cow_with_value(17, None)
            .unwrap()
            .into_mut()
            .unwrap();
        value.value = 19;
        assert_eq!(calls.get(), 1);
        assert_eq!(updates.get(17).unwrap().value, 19);
        assert_eq!(updates.len(), 1);
    }

    #[test]
    fn consuming_vec_cow_clones_only_when_vacant() {
        consuming_clone_protocol::<MaxMap<VecMap<CountedClone>>>();
    }

    #[test]
    fn consuming_btree_cow_clones_only_when_vacant() {
        consuming_clone_protocol::<MaxMap<BTreeMap<usize, CountedClone>>>();
    }

    #[test]
    fn consuming_missing_entry_neither_clones_nor_records_maximum() {
        let calls = Rc::new(Cell::new(0));
        let backing = CountedClone {
            value: 16,
            calls: calls.clone(),
        };
        for handle in [
            Cow::BTree(
                BTreeCow::Immutable {
                    value: &backing,
                    entry: None,
                },
                CowOnMut::default(),
            ),
            Cow::Vec(
                VecCow::Immutable {
                    value: &backing,
                    entry: None,
                },
                CowOnMut::default(),
            ),
        ] {
            let mut maximum = MaxIndexState::Empty;
            let result = handle.with_max_index(&mut maximum, 17).into_mut();
            assert!(matches!(result, Err(Error::CowMissingEntry)));
            assert_eq!(maximum, MaxIndexState::Empty);
            assert_eq!(calls.get(), 0);
        }
    }

    #[test]
    fn on_mut_records_max_index_once() {
        let mut value = 1;
        let mut max_index = MaxIndexState::Empty;
        let mut cow = Cow::Vec(VecCow::Mutable { value: &mut value }, CowOnMut::default())
            .with_max_index(&mut max_index, 3);

        *cow.make_mut().expect("mutable cow should remain mutable") = 2;
        *cow.make_mut().expect("mutable cow should remain mutable") = 3;

        assert_eq!(max_index, MaxIndexState::Known(3));
        assert_eq!(value, 3);
    }

    #[test]
    fn on_mut_does_not_record_max_index_on_error() {
        let value = 1;
        let mut max_index = MaxIndexState::Empty;
        let mut cow = Cow::Vec(
            VecCow::Immutable {
                value: &value,
                entry: None,
            },
            CowOnMut::default(),
        )
        .with_max_index(&mut max_index, 3);

        assert_eq!(cow.make_mut(), Err(Error::CowMissingEntry));

        assert_eq!(max_index, MaxIndexState::Empty);
    }
}
