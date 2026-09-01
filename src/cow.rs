use crate::Error;
use std::collections::btree_map::VacantEntry;
use std::ops::Deref;

pub enum Cow<'a, T: Clone> {
    BTree(BTreeCow<'a, T>, Option<Box<dyn FnOnce() + 'a>>),
    Vec(VecCow<'a, T>, Option<Box<dyn FnOnce() + 'a>>),
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
            Self::BTree(cow, on_mut) => {
                let value = cow.into_mut()?;
                if let Some(on_mut) = on_mut {
                    on_mut();
                }
                Ok(value)
            }
            Self::Vec(cow, on_mut) => {
                let value = cow.into_mut()?;
                if let Some(on_mut) = on_mut {
                    on_mut();
                }
                Ok(value)
            }
        }
    }

    pub fn make_mut(&mut self) -> Result<&mut T, Error> {
        match self {
            Self::BTree(cow, on_mut) => {
                let value = cow.make_mut()?;
                if let Some(on_mut) = on_mut.take() {
                    on_mut();
                }
                Ok(value)
            }
            Self::Vec(cow, on_mut) => {
                let value = cow.make_mut()?;
                if let Some(on_mut) = on_mut.take() {
                    on_mut();
                }
                Ok(value)
            }
        }
    }

    pub(crate) fn with_on_mut<F>(mut self, on_mut: F) -> Self
    where
        F: FnOnce() + 'a,
    {
        match &mut self {
            Self::BTree(_, callback) | Self::Vec(_, callback) => {
                *callback = Some(Box::new(on_mut));
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
    use super::{Cow, VecCow};
    use crate::Error;
    use std::cell::Cell;

    #[test]
    fn on_mut_callback_runs_once() {
        let mut value = 1;
        let callback_count = Cell::new(0);
        let mut cow = Cow::Vec(VecCow::Mutable { value: &mut value }, None)
            .with_on_mut(|| callback_count.set(callback_count.get() + 1));

        *cow.make_mut().expect("mutable cow should remain mutable") = 2;
        *cow.make_mut().expect("mutable cow should remain mutable") = 3;
        drop(cow);

        assert_eq!(callback_count.get(), 1);
        assert_eq!(value, 3);
    }

    #[test]
    fn on_mut_callback_does_not_run_on_error() {
        let value = 1;
        let callback_count = Cell::new(0);
        let mut cow = Cow::Vec(
            VecCow::Immutable {
                value: &value,
                entry: None,
            },
            None,
        )
        .with_on_mut(|| callback_count.set(callback_count.get() + 1));

        assert_eq!(cow.make_mut(), Err(Error::CowMissingEntry));
        drop(cow);

        assert_eq!(callback_count.get(), 0);
    }
}
