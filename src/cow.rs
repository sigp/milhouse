use std::collections::btree_map::VacantEntry;
use std::ops::Deref;

#[derive(Debug)]
pub enum Cow<'a, T: Clone> {
    BTree(BTreeCow<'a, T>),
}

impl<'a, T: Clone> Deref for Cow<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::BTree(cow) => cow.deref(),
        }
    }
}

impl<'a, T: Clone> Cow<'a, T> {
    pub fn to_mut(self) -> &'a mut T {
        match self {
            Self::BTree(cow) => cow.to_mut(),
        }
    }
}

pub trait CowTrait<'a, T: Clone>: Deref<Target = T> {
    fn to_mut(self) -> &'a mut T;
}

#[derive(Debug)]
pub enum BTreeCow<'a, T: Clone> {
    Immutable {
        value: &'a T,
        entry: VacantEntry<'a, usize, T>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> CowTrait<'a, T> for BTreeCow<'a, T> {
    fn to_mut(self) -> &'a mut T {
        match self {
            Self::Immutable { value, entry } => entry.insert(value.clone()),
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
