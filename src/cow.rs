use crate::Error;
use std::collections::btree_map::VacantEntry;
use std::ops::Deref;

pub enum Cow<'a, T: Clone> {
    BTree(BTreeCow<'a, T>),
    Vec(VecCow<'a, T>),
}

impl<T: Clone> Deref for Cow<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::BTree(cow) => cow.deref(),
            Self::Vec(cow) => cow.deref(),
        }
    }
}

impl<'a, T: Clone> Cow<'a, T> {
    pub fn into_mut(self) -> Result<&'a mut T, Error> {
        match self {
            Self::BTree(cow) => cow.into_mut(),
            Self::Vec(cow) => cow.into_mut(),
        }
    }

    pub fn make_mut(&mut self) -> Result<&mut T, Error> {
        match self {
            Self::BTree(cow) => cow.make_mut(),
            Self::Vec(cow) => cow.make_mut(),
        }
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
