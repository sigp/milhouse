#![allow(clippy::comparison_chain)]
#![deny(clippy::unwrap_used)]

pub mod builder;
pub mod cow;
pub mod error;
pub mod interface;
pub mod interface_iter;
pub mod iter;
pub mod leaf;
pub mod level_iter;
pub mod list;
pub mod mem;
pub mod packed_leaf;
mod repeat;
pub mod serde;
mod tests;
pub mod tree;
pub mod update_map;
pub mod utils;
pub mod vector;
pub mod prog_tree;

#[cfg(feature = "context_deserialize")]
mod context_deserialize;

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

/// Maximum depth for a tree.
///
/// We limit trees to 2^63 elements so we can avoid overflow when calculating 2^depth.
pub const MAX_TREE_DEPTH: usize = u64::BITS as usize - 1;

pub const MAX_TREE_LENGTH: u64 = 1 << MAX_TREE_DEPTH;

#[cfg(feature = "debug")]
pub trait Value: Encode + Decode + TreeHash + PartialEq + Clone + std::fmt::Debug {}

#[cfg(feature = "debug")]
impl<T> Value for T where T: Encode + Decode + TreeHash + PartialEq + Clone + std::fmt::Debug {}

#[cfg(not(feature = "debug"))]
pub trait Value: Encode + Decode + TreeHash + PartialEq + Clone {}

#[cfg(not(feature = "debug"))]
impl<T> Value for T where T: Encode + Decode + TreeHash + PartialEq + Clone {}
