use std::collections::{btree_map::Entry, BTreeMap};
use std::ops::Deref;

pub enum Cow<'a, T: Clone> {
    Immutable {
        index: usize,
        value: &'a T,
        updates: &'a mut BTreeMap<usize, T>,
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
            Cow::Immutable {
                index,
                value,
                updates,
            } => match updates.entry(index) {
                Entry::Vacant(entry) => entry.insert(value.clone()),
                Entry::Occupied(entry) => entry.into_mut(),
            },
            Cow::Mutable { value, .. } => value,
        }
    }
}
