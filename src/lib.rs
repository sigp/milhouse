#![allow(clippy::comparison_chain)]
#![deny(clippy::unwrap_used)]

pub mod builder;
pub mod cow;
pub mod diff;
pub mod error;
pub mod interface;
pub mod interface_iter;
pub mod iter;
pub mod leaf;
pub mod list;
pub mod packed_leaf;
pub mod serde;
mod tests;
pub mod tree;
pub mod utils;
pub mod vector;

pub use cow::Cow;
pub use diff::{CloneDiff, Diff, ListDiff, ResetListDiff, VectorDiff};
pub use error::Error;
pub use interface::ImmList;
pub use leaf::Leaf;
pub use list::List;
pub use packed_leaf::PackedLeaf;
pub use tree::Tree;
pub use triomphe::Arc;
pub use vector::Vector;
