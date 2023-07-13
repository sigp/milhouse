use std::borrow::Cow as StdCow;
use std::collections::btree_map::VacantEntry;
use std::ops::Deref;

pub enum Cow<'a, T: Clone> {
    BTree(BTreeCow<'a, T>),
    Vec(VecCow<'a, T>),
}

impl<'a, T: Clone> Deref for Cow<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::BTree(cow) => cow.deref(),
            Self::Vec(cow) => cow.deref(),
        }
    }
}

impl<'a, T: Clone> Cow<'a, T> {
    pub fn to_mut(self) -> &'a mut T {
        match self {
            Self::BTree(cow) => cow.to_mut(),
            Self::Vec(cow) => cow.to_mut(),
        }
    }
}

pub trait CowTrait<'a, T: Clone>: Deref<Target = T> {
    #[allow(clippy::wrong_self_convention)]
    fn to_mut(self) -> &'a mut T;
}

pub enum BTreeCow<'a, T: Clone> {
    Immutable {
        value: StdCow<'a, T>,
        entry: VacantEntry<'a, usize, T>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> CowTrait<'a, T> for BTreeCow<'a, T> {
    fn to_mut(self) -> &'a mut T {
        match self {
            Self::Immutable { value, entry } => entry.insert(value.into_owned()),
            Self::Mutable { value } => value,
        }
    }
}

impl<'a, T: Clone> Deref for BTreeCow<'a, T> {
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
        value: StdCow<'a, T>,
        entry: vec_map::VacantEntry<'a, T>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> CowTrait<'a, T> for VecCow<'a, T> {
    fn to_mut(self) -> &'a mut T {
        match self {
            Self::Immutable { value, entry } => entry.insert(value.into_owned()),
            Self::Mutable { value } => value,
        }
    }
}

impl<'a, T: Clone> Deref for VecCow<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::Immutable { value, .. } => value,
            Self::Mutable { value } => value,
        }
    }
}
