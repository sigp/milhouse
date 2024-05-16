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

pub trait Value: Encode + Decode + TreeHash + PartialEq + Clone + std::fmt::Debug {}

impl<T> Value for T where T: Encode + Decode + TreeHash + PartialEq + Clone + std::fmt::Debug {}
