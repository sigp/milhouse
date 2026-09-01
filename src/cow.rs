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
        if let Some((max_index, index)) = self.max_index.take() {
            max_index.record_insert(index);
        }
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
        match self {
            Self::BTree(cow, mut on_mut) => {
                let value = cow.into_mut()?;
                on_mut.run();
                Ok(value)
            }
            Self::Vec(cow, mut on_mut) => {
                let value = cow.into_mut()?;
                on_mut.run();
                Ok(value)
            }
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

impl<'a, T: Clone> CowTrait<'a, T> for BTreeCow<'a, T> {
    fn into_mut(self) -> Result<&'a mut T, Error> {
        match self {
            Self::Immutable { value, entry } => entry
                .ok_or(Error::CowMissingEntry)
                .map(|e| e.insert(value.clone())),
            Self::Mutable { value } => Ok(value),
        }
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

impl<'a, T: Clone> CowTrait<'a, T> for VecCow<'a, T> {
    fn into_mut(self) -> Result<&'a mut T, Error> {
        match self {
            Self::Immutable { value, entry } => entry
                .ok_or(Error::CowMissingEntry)
                .map(|e| e.insert(value.clone())),
            Self::Mutable { value } => Ok(value),
        }
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
    use super::{Cow, CowOnMut, VecCow};
    use crate::Error;
    use crate::update_map::MaxIndexState;

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
