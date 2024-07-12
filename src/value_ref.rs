use parking_lot::MappedRwLockReadGuard;
use std::ops::Deref;

/// Reference to a value within a List or Vector.
#[derive(Debug)]
pub enum ValueRef<'a, T> {
    /// The value is present in the `updates` map and is waiting to be applied.
    Pending(MappedRwLockReadGuard<'a, T>),
    /// The value is present in the tree.
    Applied(&'a T),
}

impl<'a, T> Deref for ValueRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Pending(guard) => guard.deref(),
            Self::Applied(reference) => reference,
        }
    }
}
