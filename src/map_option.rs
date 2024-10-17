use arc_swap::{access::Access, ArcSwap};
use std::ops::Deref;
use std::sync::Arc;

pub struct MapOption<'a, F: Fn(Arc<T>) -> Option<&'a R>, T, R: 'a> {
    accessor: F,
    whole_value: &'a ArcSwap<T>,
}

impl<'a, F, T, R> MapOption<'a, F, T, R>
where
    F: Fn(Arc<T>) -> Option<&'a R>,
{
    pub fn new(value: &'a ArcSwap<T>, f: F) -> Self {
        MapOption {
            accessor: f,
            whole_value: value,
        }
    }
}

pub struct MapOptionGuard<'a, T, R> {
    value: Option<&'a R>,
    parent: Arc<T>,
}

impl<'a, T, R> Deref for MapOptionGuard<'a, T, R> {
    type Target = Option<&'a R>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/*
pub trait Access<T> {
    type Guard: Deref<Target = T>;

    // Required method
    fn load(&self) -> Self::Guard;
}
*/

impl<'a, F, T, R> Access<Option<&'a R>> for MapOption<'a, F, T, R>
where
    F: Fn(&'a Arc<T>) -> Option<&'a R>,
{
    type Guard = MapOptionGuard<'a, T, R>;

    fn load(&self) -> Self::Guard {
        let loaded_value: Arc<T> = self.whole_value.load_full();
        let mut guard = MapOptionGuard {
            value: None,
            parent: loaded_value,
        };
        let value = (self.accessor)(&guard.parent);
        guard.value = value;
        guard
    }
}
