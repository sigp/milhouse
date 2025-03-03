use crate::utils::{arb_arc, arb_rwlock, opt_hash, opt_packing_depth, opt_packing_factor, Length};
use crate::{Arc, Error, Leaf, PackedLeaf, UpdateMap, Value};
use arbitrary::Arbitrary;
use educe::Educe;
use ethereum_hashing::{hash32_concat, ZERO_HASHES};
use parking_lot::RwLock;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::ops::ControlFlow;
use tree_hash::Hash256;

#[derive(Debug, Educe, Arbitrary)]
#[educe(PartialEq(bound(T: Value)), Hash)]
pub enum Tree<T: Value> {
    Leaf(Leaf<T>),
    PackedLeaf(PackedLeaf<T>),
    Node {
        #[educe(PartialEq(ignore), Hash(ignore))]
        #[arbitrary(with = arb_rwlock)]
        hash: RwLock<Hash256>,
        #[arbitrary(with = arb_arc)]
        left: Arc<Self>,
        #[arbitrary(with = arb_arc)]
        right: Arc<Self>,
    },
    Zero(usize),
}

impl<T: Value> Clone for Tree<T> {
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

impl<T: Value> Tree<T> {
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
            hash: RwLock::new(Hash256::ZERO),
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

    pub fn get_recursive(&self, index: usize, depth: usize, packing_depth: usize) -> Option<&T> {
        match self {
            Self::Leaf(Leaf { value, .. }) if depth == 0 => Some(value),
            Self::PackedLeaf(PackedLeaf { values, .. }) if depth == 0 => {
                values.get(index % T::tree_hash_packing_factor())
            }
            Self::Node { left, right, .. } if depth > 0 => {
                let new_depth = depth - 1;
                // Left
                if (index >> (new_depth + packing_depth)) & 1 == 0 {
                    left.get_recursive(index, new_depth, packing_depth)
                }
                // Right
                else {
                    right.get_recursive(index, new_depth, packing_depth)
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
                        Hash256::ZERO,
                    ))
                } else {
                    // Index lies on the right, recurse right
                    Ok(Self::node(
                        left.clone(),
                        right.with_updated_leaf(index, new_value, new_depth)?,
                        Hash256::ZERO,
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
                    Self::node(new_zero.clone(), new_zero, Hash256::ZERO)
                        .with_updated_leaf(index, new_value, depth)
                }
            }
            _ => Err(Error::UpdateLeafError),
        }
    }

    pub fn with_updated_leaves<U: UpdateMap<T>>(
        &self,
        updates: &U,
        prefix: usize,
        depth: usize,
        hashes: Option<&BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<Arc<Self>, Error> {
        let hash = opt_hash(hashes, depth, prefix).unwrap_or_default();

        match self {
            Self::Leaf(_) if depth == 0 => {
                let index = prefix;
                let value = updates
                    .get(index)
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

                let mut has_left_updates = false;
                updates.for_each_range(left_prefix, right_prefix, |_, _| {
                    has_left_updates = true;
                    ControlFlow::Break(())
                })?;
                let mut has_right_updates = false;
                updates.for_each_range(right_prefix, right_subtree_end, |_, _| {
                    has_right_updates = true;
                    ControlFlow::Break(())
                })?;

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
                            .get(index)
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

    /// Compute the number of elements stored in this subtree.
    ///
    /// This method should be avoided if possible. Prefer to read the length cached in a `List` or
    /// similar.
    pub fn compute_len(&self) -> usize {
        match self {
            Self::Leaf(_) => 1,
            Self::PackedLeaf(leaf) => leaf.values.len(),
            Self::Node { left, right, .. } => left.compute_len() + right.compute_len(),
            Self::Zero(_) => 0,
        }
    }
}

pub enum RebaseAction<'a, T> {
    // Not equal and no changes in parent nodes required.
    NotEqualNoop,
    // Not equal, but `new` should be replaced by the given node.
    NotEqualReplace(Arc<T>),
    // Nodes are already exactly equal and pointer equal.
    EqualNoop,
    // Nodes are exactly equal and `new` should be replaced by the given node.
    EqualReplace(&'a Arc<T>),
}

pub enum IntraRebaseAction<T> {
    Noop,
    Replace(Arc<T>),
}

impl<T: Value> Tree<T> {
    pub fn rebase_on<'a>(
        orig: &'a Arc<Self>,
        base: &'a Arc<Self>,
        lengths: Option<(Length, Length)>,
        full_depth: usize,
    ) -> Result<RebaseAction<'a, Self>, Error> {
        if Arc::ptr_eq(orig, base) {
            return Ok(RebaseAction::EqualNoop);
        }
        match (&**orig, &**base) {
            (Self::Leaf(l1), Self::Leaf(l2)) => {
                if l1.value == l2.value {
                    Ok(RebaseAction::EqualReplace(base))
                } else {
                    Ok(RebaseAction::NotEqualNoop)
                }
            }
            (Self::PackedLeaf(l1), Self::PackedLeaf(l2)) => {
                if l1.values == l2.values {
                    Ok(RebaseAction::EqualReplace(base))
                } else {
                    Ok(RebaseAction::NotEqualNoop)
                }
            }
            (Self::Zero(z1), Self::Zero(z2)) if z1 == z2 => Ok(RebaseAction::EqualReplace(base)),
            (
                Self::Node {
                    hash: orig_hash_lock,
                    left: ref l1,
                    right: ref r1,
                },
                Self::Node {
                    hash: base_hash_lock,
                    left: ref l2,
                    right: ref r2,
                },
            ) if full_depth > 0 => {
                use RebaseAction::*;

                let orig_hash = *orig_hash_lock.read();
                let base_hash = *base_hash_lock.read();

                // If hashes *and* lengths are equal then we can short-cut the recursion
                // and immediately replace `orig` by the `base` node. If `lengths` are `None`
                // then we know they are already equal (e.g. we're in a vector).
                if !orig_hash.is_zero()
                    && orig_hash == base_hash
                    && lengths.is_none_or(|(orig_length, base_length)| orig_length == base_length)
                {
                    return Ok(EqualReplace(base));
                }

                let new_full_depth = full_depth - 1;
                let (left_lengths, right_lengths) = lengths
                    .map(|(orig_length, base_length)| {
                        let max_left_length = Length(1 << new_full_depth);
                        let orig_left_length = std::cmp::min(orig_length, max_left_length);
                        let orig_right_length =
                            Length(orig_length.as_usize() - orig_left_length.as_usize());

                        let base_left_length = std::cmp::min(base_length, max_left_length);
                        let base_right_length =
                            Length(base_length.as_usize() - base_left_length.as_usize());
                        (
                            (orig_left_length, base_left_length),
                            (orig_right_length, base_right_length),
                        )
                    })
                    .unzip();

                let left_action = Tree::rebase_on(l1, l2, left_lengths, new_full_depth)?;
                let right_action = Tree::rebase_on(r1, r2, right_lengths, new_full_depth)?;

                match (left_action, right_action) {
                    (NotEqualNoop, NotEqualNoop | EqualNoop) | (EqualNoop, NotEqualNoop) => {
                        Ok(NotEqualNoop)
                    }
                    (EqualNoop, EqualNoop) => Ok(EqualNoop),
                    (NotEqualNoop | EqualNoop, NotEqualReplace(new_right)) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: l1.clone(),
                            right: new_right,
                        })))
                    }
                    (NotEqualNoop | EqualNoop, EqualReplace(new_right)) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: l1.clone(),
                            right: new_right.clone(),
                        })))
                    }
                    (NotEqualReplace(new_left), NotEqualNoop | EqualNoop) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: new_left,
                            right: r1.clone(),
                        })))
                    }
                    (NotEqualReplace(new_left), NotEqualReplace(new_right)) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: new_left,
                            right: new_right,
                        })))
                    }
                    (NotEqualReplace(new_left), EqualReplace(new_right)) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: new_left,
                            right: new_right.clone(),
                        })))
                    }
                    (EqualReplace(new_left), NotEqualNoop) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: new_left.clone(),
                            right: r1.clone(),
                        })))
                    }
                    (EqualReplace(new_left), NotEqualReplace(new_right)) => {
                        Ok(NotEqualReplace(Arc::new(Self::Node {
                            hash: RwLock::new(orig_hash),
                            left: new_left.clone(),
                            right: new_right,
                        })))
                    }
                    (EqualReplace(_), EqualReplace(_)) | (EqualReplace(_), EqualNoop) => {
                        Ok(EqualReplace(base))
                    }
                }
            }
            (Self::Zero(_), _) | (_, Self::Zero(_)) => Ok(RebaseAction::NotEqualNoop),
            (Self::Node { .. }, Self::Node { .. }) => Err(Error::InvalidRebaseNode),
            (Self::Leaf(_) | Self::PackedLeaf(_), _) | (_, Self::Leaf(_) | Self::PackedLeaf(_)) => {
                Err(Error::InvalidRebaseLeaf)
            }
        }
    }

    /// FIXME(sproul): descr
    ///
    /// `known_subtrees`: map from `(depth, tree_hash_root)` to `Arc<Node>`.
    pub fn intra_rebase(
        orig: &Arc<Self>,
        known_subtrees: &mut HashMap<(usize, Hash256), Arc<Self>>,
        current_depth: usize,
    ) -> Result<IntraRebaseAction<Self>, Error> {
        match &**orig {
            Self::Leaf(_) | Self::PackedLeaf(_) | Self::Zero(_) => Ok(IntraRebaseAction::Noop),
            Self::Node { hash, left, right } if current_depth > 0 => {
                let hash = *hash.read();

                // Tree must be fully hashed prior to intra-rebase.
                if hash.is_zero() {
                    return Err(Error::IntraRebaseZeroHash);
                }

                if let Some(known_subtree) = known_subtrees.get(&(current_depth, hash)) {
                    // Node is already known from elsewhere in the tree. We can replace it without
                    // looking at further subtrees.
                    return Ok(IntraRebaseAction::Replace(known_subtree.clone()));
                }

                let left_action = Self::intra_rebase(left, known_subtrees, current_depth - 1)?;
                let right_action = Self::intra_rebase(right, known_subtrees, current_depth - 1)?;

                let action = match (left_action, right_action) {
                    (IntraRebaseAction::Noop, IntraRebaseAction::Noop) => IntraRebaseAction::Noop,
                    (IntraRebaseAction::Noop, IntraRebaseAction::Replace(new_right)) => {
                        IntraRebaseAction::Replace(Self::node(left.clone(), new_right, hash))
                    }
                    (IntraRebaseAction::Replace(new_left), IntraRebaseAction::Noop) => {
                        IntraRebaseAction::Replace(Self::node(new_left, right.clone(), hash))
                    }
                    (
                        IntraRebaseAction::Replace(new_left),
                        IntraRebaseAction::Replace(new_right),
                    ) => IntraRebaseAction::Replace(Self::node(new_left, new_right, hash)),
                };

                // Add the new version of this node to the known subtrees.
                match &action {
                    IntraRebaseAction::Noop => {
                        let existing_entry =
                            known_subtrees.insert((current_depth, hash), orig.clone());
                        // FIXME(sproul): maybe remove this assert/error
                        assert!(existing_entry.is_none());
                    }
                    IntraRebaseAction::Replace(new) => {
                        let existing_entry =
                            known_subtrees.insert((current_depth, hash), new.clone());
                        // FIXME(sproul): maybe remove this assert/error
                        assert!(existing_entry.is_none());
                    }
                }
                Ok(action)
            }
            Self::Node { .. } => Err(Error::IntraRebaseZeroDepth),
        }
    }
}

impl<T: Value + Send + Sync> Tree<T> {
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
            Self::Zero(depth) => Hash256::from(ZERO_HASHES[*depth]),
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
                        Hash256::from(hash32_concat(left_hash.as_slice(), right_hash.as_slice()));
                    *hash.write() = tree_hash;
                    tree_hash
                }
            }
        }
    }
}
