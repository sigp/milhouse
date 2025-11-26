use crate::{Arc, Error, Tree, Value, builder::Builder, utils::opt_packing_factor};
use educe::Educe;
use ethereum_hashing::hash32_concat;
use parking_lot::RwLock;
use tree_hash::Hash256;

/// The size of each binary subtree in a progressive tree is `4^prog_depth` at depth `prog_depth`.
const PROG_TREE_EXPONENT: usize = 4;

/// This scaling factor is used to convert between a 4-based progressive depth and a 2-based
/// depth for a binary subtree.
///
/// It is defined such that the binary subtree at progressive depth `prog_depth` has depth
/// `PROG_TREE_BINARY_SCALE * prog_depth`. This comes from this equation:
///
/// PROG_TREE_EXPONENT^prog_depth = 2^binary_depth
///
/// Hence:
///
/// binary_depth = log2(PROG_TREE_EXPONENT^prog_depth)
///
/// Knowing PROG_TREE_EXPONENT is `2^k` for some `k`, this becomes:
///
/// binary_depth = log2(2^(k * prog_depth))
///              = k * prog_depth
///
/// This `k` is the scaling factor, equal to `log2(PROG_TREE_EXPONENT)`.
const PROG_TREE_BINARY_SCALE: usize = PROG_TREE_EXPONENT.trailing_zeros() as usize;

/// Tree type for the implementation of `ProgressiveList`.
#[derive(Debug, Educe)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[educe(PartialEq(bound(T: Value)), Hash)]
pub enum ProgTree<T: Value> {
    ProgZero,
    ProgNode {
        #[educe(PartialEq(ignore), Hash(ignore))]
        #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_rwlock))]
        hash: RwLock<Hash256>,
        #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_arc))]
        left: Arc<Self>,
        #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_arc))]
        right: Arc<Tree<T>>,
    },
}

impl<T: Value> ProgTree<T> {
    pub fn empty() -> Self {
        Self::ProgZero
    }

    /// The number of values that can be stored in the single subtree at `prog_depth` itself.
    pub fn capacity_at_depth(prog_depth: u32) -> usize {
        let capacity_pre_packing = match prog_depth.checked_sub(1) {
            None => 0,
            Some(depth_minus_one) => PROG_TREE_EXPONENT.pow(depth_minus_one),
        };
        capacity_pre_packing * opt_packing_factor::<T>().unwrap_or(1)
    }

    /// The number of values that be stored in the whole progressive tree up to and including
    /// the layer at `prog_depth`.
    pub fn total_capacity_at_depth(prog_depth: u32) -> usize {
        let total_capacity_pre_packing =
            PROG_TREE_EXPONENT.pow(prog_depth).saturating_sub(1) / (PROG_TREE_EXPONENT - 1);
        total_capacity_pre_packing * opt_packing_factor::<T>().unwrap_or(1)
    }

    /// Calculate the depth for the binary subtree at `prog_depth`.
    pub fn prog_depth_to_binary_depth(prog_depth: u32) -> usize {
        match prog_depth.checked_sub(1) {
            None => 0,
            Some(prog_depth_minus_one) => {
                // FIXME: work out why we don't need to sub the packing depth here, seems weird
                let binary_depth_pre_packing =
                    PROG_TREE_BINARY_SCALE * prog_depth_minus_one as usize;
                binary_depth_pre_packing
            }
        }
    }

    // TODO: add a bulk builder
    fn push_recursive(
        &self,
        value: T,
        current_length: usize,
        prog_depth: u32,
    ) -> Result<Self, Error> {
        match self {
            // Expand this zero into a new right node for our element.
            Self::ProgZero => {
                // The `prog_depth` of the new right subtree is `prog_depth + 1`.
                let subtree_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                let mut tree_builder = Builder::<T>::new(subtree_depth, 0)?;
                tree_builder.push(value)?;
                let (new_right, _, _) = tree_builder.finish()?;

                Ok(Self::ProgNode {
                    hash: RwLock::new(Hash256::ZERO),
                    left: Arc::new(Self::ProgZero),
                    right: new_right,
                })
            }
            Self::ProgNode {
                hash: _,
                left,
                right,
            } => {
                // Case 1: new element already fits inside the right-tree at prog_depth + 1.
                let total_capacity_at_depth = Self::total_capacity_at_depth(prog_depth + 1);
                if current_length < total_capacity_at_depth {
                    let index =
                        current_length.saturating_sub(Self::total_capacity_at_depth(prog_depth));

                    // Our right subtree can hold 4^prog_depth entries. We need to work out
                    // a 2-based depth for this sub tree, such that the subtree holds
                    // 2^subtree_depth entries.
                    let subtree_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                    let new_right = right.with_updated_leaf(index, value, subtree_depth)?;

                    // FIXME: remove assert
                    assert!(matches!(**left, Self::ProgZero));

                    Ok(Self::ProgNode {
                        hash: RwLock::new(Hash256::ZERO),
                        left: left.clone(),
                        right: new_right,
                    })
                } else {
                    // Case 2: new element does not fit inside this right-tree: recurse to the next
                    // level on the left.
                    let new_left = left.push_recursive(value, current_length, prog_depth + 1)?;

                    Ok(Self::ProgNode {
                        hash: RwLock::new(Hash256::ZERO),
                        left: Arc::new(new_left),
                        right: right.clone(),
                    })
                }
            }
        }
    }

    pub fn push(&self, value: T, current_length: usize) -> Result<Self, Error> {
        self.push_recursive(value, current_length, 0)
    }
}

impl<T: Value + Send + Sync> ProgTree<T> {
    pub fn tree_hash(&self) -> Hash256 {
        match self {
            Self::ProgZero => Hash256::ZERO,
            Self::ProgNode { hash, left, right } => {
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
