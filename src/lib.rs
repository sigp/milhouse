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
use typenum::{
    assert_type_eq, generic_const_mappings::U, IsLessOrEqual, Unsigned, B1, U9223372036854775808,
};

/// Maximum depth for a tree.
///
/// We limit trees to 2^63 elements so we can avoid overflow when calculating 2^depth.
pub const MAX_TREE_DEPTH: usize = u64::BITS as usize - 1;

pub const MAX_TREE_LENGTH: usize = 1 << MAX_TREE_DEPTH;

/// Maximum length of lists and vectors.
pub type MaxTreeLength = U9223372036854775808;

// Consistency check on `MAX_TREE_LENGTH` and `MaxTreeLength`.
assert_type_eq!(MaxTreeLength, U<MAX_TREE_LENGTH>);

/// Trait to assert the bounds on list and vector lengths
pub trait ValidN: Unsigned + IsLessOrEqual<MaxTreeLength, Output = B1> {}
impl<N: Unsigned + IsLessOrEqual<MaxTreeLength, Output = B1>> ValidN for N {}

pub trait Value: Encode + Decode + TreeHash + PartialEq + Clone {}

impl<T> Value for T where T: Encode + Decode + TreeHash + PartialEq + Clone {}
