#![allow(clippy::comparison_chain)]
#![deny(clippy::unwrap_used)]

pub mod builder;
pub mod cow;
pub mod error;
pub mod interface;
pub mod interface_iter;
pub mod iter;
pub mod leaf;
pub mod list;
pub mod packed_leaf;
mod repeat;
pub mod serde;
mod tests;
pub mod tree;
pub mod update_map;
pub mod utils;
pub mod vector;

pub use cow::Cow;
pub use error::Error;
pub use interface::ImmList;
pub use leaf::Leaf;
pub use list::List;
pub use packed_leaf::PackedLeaf;
pub use tree::Tree;
pub use triomphe::Arc;
pub use update_map::UpdateMap;
pub use vector::Vector;

use ssz::{Decode, Encode};
use tree_hash::TreeHash;

pub trait PendingUpdates {
    fn apply(&mut self) -> Result<(), Error> {
        Ok(())
    }
}

pub trait Value: Encode + Decode + TreeHash + PartialEq + Clone + PendingUpdates {}

impl<T> Value for T where T: Encode + Decode + TreeHash + PartialEq + Clone + PendingUpdates {}

// Default impls for known types
impl PendingUpdates for u8 {}
impl PendingUpdates for u16 {}
impl PendingUpdates for u32 {}
impl PendingUpdates for u64 {}
impl PendingUpdates for u128 {}
impl PendingUpdates for tree_hash::Hash256 {}
