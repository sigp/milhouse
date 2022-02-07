use std::collections::btree_map::VacantEntry;
use std::ops::Deref;

pub enum Cow<'a, T: Clone> {
    Immutable {
        value: &'a T,
        entry: VacantEntry<'a, usize, T>,
    },
    Mutable {
        value: &'a mut T,
    },
}

impl<'a, T: Clone> Deref for Cow<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Cow::Immutable { value, .. } => value,
            Cow::Mutable { value, .. } => value,
        }
    }
}

impl<'a, T: Clone> Cow<'a, T> {
    pub fn to_mut(self) -> &'a mut T {
        match self {
            Cow::Immutable { value, entry } => entry.insert(value.clone()),
            Cow::Mutable { value } => value,
        }
    }
}
