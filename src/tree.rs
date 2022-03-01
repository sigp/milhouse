use crate::utils::{opt_hash, opt_packing_depth, opt_packing_factor};
use crate::{Arc, Error, Leaf, PackedLeaf};
use derivative::Derivative;
use eth2_hashing::{hash32_concat, ZERO_HASHES};
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};
use ssz::{Decode, Encode};
use ssz_derive::{Decode, Encode};
use std::collections::BTreeMap;
use tree_hash::{Hash256, TreeHash};

#[derive(Debug, Derivative)]
#[derivative(PartialEq, Hash)]
pub enum Tree<T: TreeHash + Clone> {
    Leaf(Leaf<T>),
    PackedLeaf(PackedLeaf<T>),
    Node {
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        hash: RwLock<Hash256>,
        left: Arc<Self>,
        right: Arc<Self>,
    },
    Zero(usize),
}

impl<T: TreeHash + Clone> Clone for Tree<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Node { hash, left, right } => Self::Node {
                hash: RwLock::new(*hash.read()),
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

    pub fn node(left: Arc<Self>, right: Arc<Self>, hash: Hash256) -> Arc<Self> {
        Arc::new(Self::Node {
            hash: RwLock::new(hash),
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

    pub fn leaf_with_hash(value: T, hash: Hash256) -> Arc<Self> {
        Arc::new(Self::Leaf(Leaf::with_hash(value, hash)))
    }

    pub fn node_unboxed(left: Arc<Self>, right: Arc<Self>) -> Self {
        Self::Node {
            hash: RwLock::new(Hash256::zero()),
            left,
            right,
        }
    }

    pub fn zero_unboxed(depth: usize) -> Self {
        Self::Zero(depth)
    }

    pub fn leaf_unboxed(value: T) -> Self {
        Self::Leaf(Leaf::new(value))
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

    /// Create a new tree where the `index`th leaf is set to `new_value`.
    ///
    /// NOTE: callers are responsible for bounds-checking `index` before calling this function.
    pub fn with_updated_leaf(
        &self,
        index: usize,
        new_value: T,
        depth: usize,
    ) -> Result<Arc<Self>, Error> {
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
                        Hash256::zero(),
                    ))
                } else {
                    // Index lies on the right, recurse right
                    Ok(Self::node(
                        left.clone(),
                        right.with_updated_leaf(index, new_value, new_depth)?,
                        Hash256::zero(),
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
                    Self::node(new_zero.clone(), new_zero, Hash256::zero())
                        .with_updated_leaf(index, new_value, depth)
                }
            }
            _ => Err(Error::UpdateLeafError),
        }
    }

    pub fn with_updated_leaves(
        &self,
        updates: &BTreeMap<usize, T>,
        prefix: usize,
        depth: usize,
        hashes: Option<&BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<Arc<Self>, Error> {
        let hash = opt_hash(hashes, depth, prefix).unwrap_or_default();

        match self {
            Self::Leaf(_) if depth == 0 => {
                let index = prefix;
                let value = updates
                    .get(&index)
                    .cloned()
                    .ok_or(Error::LeafUpdateMissing { index })?;
                Ok(Self::leaf_with_hash(value, hash))
            }
            Self::PackedLeaf(packed_leaf) if depth == 0 => Ok(Arc::new(Self::PackedLeaf(
                packed_leaf.update(prefix, hash, updates)?,
            ))),
            Self::Node { left, right, .. } if depth > 0 => {
                let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
                let new_depth = depth - 1;
                let left_prefix = prefix;
                let right_prefix = prefix | (1 << (new_depth + packing_depth));
                let right_subtree_end = prefix + (1 << (depth + packing_depth));

                let has_left_updates = updates.range(left_prefix..right_prefix).next().is_some();
                let has_right_updates = updates
                    .range(right_prefix..right_subtree_end)
                    .next()
                    .is_some();

                // Must have some updates else this recursive branch is a complete waste of time.
                if !has_left_updates && !has_right_updates {
                    return Err(Error::NodeUpdatesMissing { prefix });
                }

                let new_left = if has_left_updates {
                    left.with_updated_leaves(updates, left_prefix, new_depth, hashes)?
                } else {
                    left.clone()
                };
                let new_right = if has_right_updates {
                    right.with_updated_leaves(updates, right_prefix, new_depth, hashes)?
                } else {
                    right.clone()
                };

                Ok(Self::node(new_left, new_right, hash))
            }
            Self::Zero(zero_depth) if *zero_depth == depth => {
                if depth == 0 {
                    if opt_packing_factor::<T>().is_some() {
                        let packed_leaf = PackedLeaf::empty().update(prefix, hash, updates)?;
                        Ok(Arc::new(Self::PackedLeaf(packed_leaf)))
                    } else {
                        let index = prefix;
                        let value = updates
                            .get(&index)
                            .cloned()
                            .ok_or(Error::LeafUpdateMissing { index })?;
                        Ok(Self::leaf_with_hash(value, hash))
                    }
                } else {
                    // Split zero node into a node with left and right and recurse.
                    let new_zero = Self::zero(depth - 1);
                    Self::node(new_zero.clone(), new_zero, hash)
                        .with_updated_leaves(updates, prefix, depth, hashes)
                }
            }
            _ => Err(Error::UpdateLeavesError),
        }
    }
}

impl<T: PartialEq + TreeHash + Clone + Encode + Decode> Tree<T> {
    pub fn diff(
        &self,
        other: &Self,
        prefix: usize,
        depth: usize,
        diff: &mut TreeDiff<T>,
    ) -> Result<(), Error> {
        match (self, other) {
            (Self::Leaf(l1), Self::Leaf(l2)) if depth == 0 => {
                if l1.value != l2.value {
                    let hash = *l2.hash.read();
                    diff.hashes.insert((depth, prefix), hash);
                    diff.leaves.insert(prefix, (*l2.value).clone());
                }
                Ok(())
            }
            (Self::PackedLeaf(l1), Self::PackedLeaf(l2)) if depth == 0 => {
                let mut equal = true;
                for i in 0..l2.values.len() {
                    let v2 = &l2.values[i];
                    match l1.values.get(i) {
                        Some(v1) if v1 == v2 => continue,
                        _ => {
                            equal = false;
                            let index = prefix | i;
                            diff.leaves.insert(index, v2.clone());
                        }
                    }
                }
                if !equal {
                    let hash = *l2.hash.read();
                    diff.hashes.insert((depth, prefix), hash);
                }
                Ok(())
            }
            (Self::Zero(z1), Self::Zero(z2)) if z1 == z2 && *z1 == depth => Ok(()),
            (
                Self::Node {
                    hash: h1,
                    left: l1,
                    right: r1,
                },
                Self::Node {
                    hash: h2,
                    left: l2,
                    right: r2,
                },
            ) if depth > 0 => {
                let h1 = *h1.read();
                let h2 = *h2.read();

                if h1 != h2 || h1.is_zero() {
                    diff.hashes.insert((depth, prefix), h2);

                    let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
                    let new_depth = depth - 1;
                    let left_prefix = prefix;
                    let right_prefix = prefix | (1 << (new_depth + packing_depth));

                    l1.diff(l2, left_prefix, new_depth, diff)?;
                    r1.diff(r2, right_prefix, new_depth, diff)?;
                }
                Ok(())
            }
            (Self::Zero(_), rhs) => rhs.add_to_diff(prefix, depth, diff),
            (_, Self::Zero(_)) => Err(Error::InvalidDiffDeleteNotSupported),
            (Self::Leaf(_) | Self::PackedLeaf(_), _) | (_, Self::Leaf(_) | Self::PackedLeaf(_)) => {
                Err(Error::InvalidDiffLeaf)
            }
            (Self::Node { .. }, Self::Node { .. }) => Err(Error::InvalidDiffNode),
        }
    }

    /// Add every node in this subtree to the diff.
    fn add_to_diff(
        &self,
        prefix: usize,
        depth: usize,
        diff: &mut TreeDiff<T>,
    ) -> Result<(), Error> {
        match self {
            Self::Leaf(leaf) if depth == 0 => {
                diff.hashes.insert((depth, prefix), *leaf.hash.read());
                diff.leaves.insert(prefix, (*leaf.value).clone());
                Ok(())
            }
            Self::PackedLeaf(packed_leaf) if depth == 0 => {
                diff.hashes
                    .insert((depth, prefix), *packed_leaf.hash.read());
                for (i, value) in packed_leaf.values.iter().enumerate() {
                    diff.leaves.insert(prefix | i, value.clone());
                }
                Ok(())
            }
            Self::Node { hash, left, right } if depth > 0 => {
                diff.hashes.insert((depth, prefix), *hash.read());

                let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
                let new_depth = depth - 1;
                let left_prefix = prefix;
                let right_prefix = prefix | (1 << (new_depth + packing_depth));

                left.add_to_diff(left_prefix, new_depth, diff)?;
                right.add_to_diff(right_prefix, new_depth, diff)?;
                Ok(())
            }
            Self::Zero(_) => Ok(()),
            _ => Err(Error::AddToDiffError),
        }
    }
}

#[derive(Debug, PartialEq, Encode, Decode, Deserialize, Serialize, Derivative)]
#[derivative(Default(bound = "T: TreeHash + Clone"))]
pub struct TreeDiff<T: TreeHash + Clone + Encode + Decode> {
    pub leaves: BTreeMap<usize, T>,
    /// Map from `(depth, prefix)` to node hash.
    pub hashes: BTreeMap<(usize, usize), Hash256>,
}

impl<T: TreeHash + Clone + Send + Sync> Tree<T> {
    pub fn tree_hash(&self) -> Hash256 {
        match self {
            Self::Leaf(Leaf { hash, value }) => {
                // FIXME(sproul): upgradeable RwLock?
                let read_lock = hash.read();
                let existing_hash = *read_lock;
                drop(read_lock);

                // NOTE: We re-compute the hash whenever it is non-zero. Computed hashes may
                // legitimately be zero, but this only occurs at the leaf level when the value is
                // entirely zeroes (e.g. [0u64, 0, 0, 0]). In order to avoid storing an
                // `Option<Hash256>` we choose to re-compute the hash in this case. In practice
                // this is unlikely to provide any performance penalty except at very small list
                // lengths (<= 32), because a node higher in the tree will cache a non-zero hash
                // preventing its children from being visited more than once.
                if !existing_hash.is_zero() {
                    existing_hash
                } else {
                    let tree_hash = value.tree_hash_root();
                    *hash.write() = tree_hash;
                    tree_hash
                }
            }
            Self::PackedLeaf(leaf) => leaf.tree_hash(),
            Self::Zero(depth) => Hash256::from_slice(&ZERO_HASHES[*depth]),
            Self::Node { hash, left, right } => {
                let read_lock = hash.read();
                let existing_hash = *read_lock;
                drop(read_lock);

                if !existing_hash.is_zero() {
                    existing_hash
                } else {
                    // Parallelism goes brrrr.
                    let (left_hash, right_hash) =
                        rayon::join(|| left.tree_hash(), || right.tree_hash());
                    let tree_hash =
                        Hash256::from(hash32_concat(left_hash.as_bytes(), right_hash.as_bytes()));
                    *hash.write() = tree_hash;
                    tree_hash
                }
            }
        }
    }
}
