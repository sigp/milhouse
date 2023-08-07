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

    pub fn make_mut(&mut self) -> &mut T {
        match self {
            Self::BTree(cow) => cow.make_mut(),
            Self::Vec(cow) => cow.make_mut(),
        }
    }
}

pub trait CowTrait<'a, T: Clone>: Deref<Target = T> {
    #[allow(clippy::wrong_self_convention)]
    fn to_mut(self) -> &'a mut T;

    fn make_mut(&mut self) -> &mut T;
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
    fn to_mut(self) -> &'a mut T {
        match self {
            Self::Immutable { value, entry } => {
                entry.expect("Cow entry must be Some").insert(value.clone())
            }
            Self::Mutable { value } => value,
        }
    }

    fn make_mut(&mut self) -> &mut T {
        match self {
            Self::Mutable { value } => value,
            Self::Immutable { entry, value } => {
                let value_mut_ref = entry
                    .take()
                    .expect("Cow entry must be Some")
                    .insert(value.clone());
                *self = Self::Mutable {
                    value: value_mut_ref,
                };
                self.make_mut()
            }
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
        value: &'a T,
        entry: Option<vec_map::VacantEntry<'a, T>>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> CowTrait<'a, T> for VecCow<'a, T> {
    fn to_mut(self) -> &'a mut T {
        match self {
            Self::Immutable { value, entry } => {
                entry.expect("Cow entry must be Some").insert(value.clone())
            }
            Self::Mutable { value } => value,
        }
    }

    fn make_mut(&mut self) -> &mut T {
        match self {
            Self::Mutable { value } => value,
            Self::Immutable { entry, value } => {
                let value_mut_ref = entry
                    .take()
                    .expect("Cow entry must be Some")
                    .insert(value.clone());
                *self = Self::Mutable {
                    value: value_mut_ref,
                };
                self.make_mut()
            }
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
