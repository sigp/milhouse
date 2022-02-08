use sharded_slab::{Clear, Config};
use std::sync::Arc;

pub enum SlabConfig {}

impl Config for SlabConfig {
    // Just use the defaults
}

pub type OwnedRef<T> = sharded_slab::pool::OwnedRef<T, SlabConfig>;

#[derive(Debug, Clone)]
pub struct Pool<T: Clear + Default> {
    inner: Arc<sharded_slab::pool::Pool<T, SlabConfig>>,
}

impl<T: Clear + Default> Pool<T> {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(sharded_slab::pool::Pool::new_with_config::<SlabConfig>()),
        }
    }

    pub fn insert(&self, val: T) -> OwnedRef<T> {
        let mut obj = self
            .inner
            .clone()
            .create_owned()
            .expect("pool should have capacity");
        *obj = val;
        obj.downgrade()
    }
}
