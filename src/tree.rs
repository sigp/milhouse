use crate::utils::{opt_packing_depth, opt_packing_factor};
use crate::{Error, Leaf, PackedLeaf};
use derivative::Derivative;
use eth2_hashing::{hash32_concat, ZERO_HASHES};
use parking_lot::RwLock;
use std::sync::Arc;
use tree_hash::{Hash256, TreeHash};

#[derive(Debug, Derivative)]
#[derivative(PartialEq, Hash)]
pub enum Tree<T: TreeHash + Clone> {
    Leaf(Leaf<T>),
    PackedLeaf(PackedLeaf<T>),
    Node {
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        hash: RwLock<Option<Hash256>>,
        left: Arc<Self>,
        right: Arc<Self>,
    },
    Zero(usize),
}

impl<T: TreeHash + Clone> Clone for Tree<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Node { hash, left, right } => Self::Node {
                hash: RwLock::new(hash.read().as_ref().cloned()),
                left: left.clone(),
                right: right.clone(),
            },
            Self::Leaf(leaf) => Self::Leaf(leaf.clone()),
            Self::PackedLeaf(leaf) => Self::PackedLeaf(leaf.clone()),
            Self::Zero(depth) => Self::Zero(*depth),
        }
    }
}

impl<T: TreeHash + Clone> Tree<T> {
    pub fn empty(depth: usize) -> Arc<Self> {
        Self::zero(depth)
    }

    pub fn node(left: Arc<Self>, right: Arc<Self>) -> Arc<Self> {
        Arc::new(Self::Node {
            hash: RwLock::new(None),
            left,
            right,
        })
    }

    pub fn zero(depth: usize) -> Arc<Self> {
        Arc::new(Self::Zero(depth))
    }

    pub fn leaf(value: T) -> Arc<Self> {
        Arc::new(Self::Leaf(Leaf::new(value)))
    }

    pub fn get(&self, index: usize, depth: usize) -> Option<&T> {
        match self {
            Self::Leaf(Leaf { value, .. }) if depth == 0 => Some(value),
            Self::PackedLeaf(PackedLeaf { values, .. }) if depth == 0 => {
                values.get(index % T::tree_hash_packing_factor())
            }
            Self::Node { left, right, .. } if depth > 0 => {
                let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
                let new_depth = depth - 1;
                // Left
                if (index >> (new_depth + packing_depth)) & 1 == 0 {
                    left.get(index, new_depth)
                }
                // Right
                else {
                    right.get(index, new_depth)
                }
            }
            _ => None,
        }
    }

    pub fn with_updated_leaf(
        &self,
        index: usize,
        new_value: T,
        depth: usize,
    ) -> Result<Arc<Self>, Error> {
        // FIXME: check index less than 2^depth
        match self {
            Self::Leaf(_) if depth == 0 => Ok(Self::leaf(new_value)),
            Self::PackedLeaf(leaf) if depth == 0 => Ok(Arc::new(Self::PackedLeaf(
                leaf.insert_at_index(index, new_value)?,
            ))),
            Self::Node { left, right, .. } if depth > 0 => {
                let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
                let new_depth = depth - 1;
                if (index >> (new_depth + packing_depth)) & 1 == 0 {
                    // Index lies on the left, recurse left
                    Ok(Self::node(
                        left.with_updated_leaf(index, new_value, new_depth)?,
                        right.clone(),
                    ))
                } else {
                    // Index lies on the right, recurse right
                    Ok(Self::node(
                        left.clone(),
                        right.with_updated_leaf(index, new_value, new_depth)?,
                    ))
                }
            }
            Self::Zero(zero_depth) if *zero_depth == depth => {
                if depth == 0 {
                    if opt_packing_factor::<T>().is_some() {
                        Ok(Arc::new(Self::PackedLeaf(PackedLeaf::single(new_value))))
                    } else {
                        Ok(Self::leaf(new_value))
                    }
                } else {
                    // Split zero node into a node with left and right, and recurse into
                    // the appropriate subtree
                    let new_zero = Self::zero(depth - 1);
                    Self::node(new_zero.clone(), new_zero)
                        .with_updated_leaf(index, new_value, depth)
                }
            }
            _ => Err(Error::Oops),
        }
    }

    pub fn tree_hash(&self) -> Hash256 {
        match self {
            Self::Leaf(Leaf { hash, value }) => {
                // FIXME(sproul): upgradeable RwLock?
                let read_lock = hash.read();
                let existing_hash = *read_lock;
                drop(read_lock);
                if let Some(hash) = existing_hash {
                    hash
                } else {
                    let tree_hash = value.tree_hash_root();
                    *hash.write() = Some(tree_hash);
                    tree_hash
                }
            }
            Self::PackedLeaf(leaf) => leaf.tree_hash(),
            Self::Zero(depth) => Hash256::from_slice(&ZERO_HASHES[*depth]),
            Self::Node { hash, left, right } => {
                let read_lock = hash.read();
                let existing_hash = *read_lock;
                drop(read_lock);
                if let Some(hash) = existing_hash {
                    hash
                } else {
                    let left_hash = left.tree_hash();
                    let right_hash = right.tree_hash();
                    let tree_hash =
                        Hash256::from(hash32_concat(left_hash.as_bytes(), right_hash.as_bytes()));
                    *hash.write() = Some(tree_hash);
                    tree_hash
                }
            }
        }
    }
}
