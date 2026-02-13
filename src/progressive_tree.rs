use crate::{
    Arc, Error, Tree, Value,
    builder::Builder,
    iter::Iter,
    utils::{Length, opt_packing_factor},
};
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
pub enum ProgressiveTree<T: Value> {
    ProgressiveZero,
    ProgressiveNode {
        #[educe(PartialEq(ignore), Hash(ignore))]
        #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_rwlock))]
        hash: RwLock<Hash256>,
        #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_arc))]
        left: Arc<Tree<T>>,
        #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_arc))]
        right: Arc<Self>,
    },
}

impl<T: Value> Clone for ProgressiveTree<T> {
    fn clone(&self) -> Self {
        match self {
            Self::ProgressiveNode { hash, left, right } => Self::ProgressiveNode {
                hash: RwLock::new(*hash.read()),
                left: left.clone(),
                right: right.clone(),
            },
            Self::ProgressiveZero => Self::ProgressiveZero,
        }
    }
}

impl<T: Value> ProgressiveTree<T> {
    pub fn empty() -> Self {
        Self::ProgressiveZero
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
                PROG_TREE_BINARY_SCALE * prog_depth_minus_one as usize
            }
        }
    }

    /// Build a `ProgressiveTree` efficiently from an iterator.
    /// Only creates one `Builder` per subtree.
    pub fn build_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut iter = iter.into_iter();
        let mut subtrees: Vec<Arc<Tree<T>>> = Vec::new();
        let mut prog_depth = 1u32;

        loop {
            let capacity = Self::capacity_at_depth(prog_depth);
            let binary_depth = Self::prog_depth_to_binary_depth(prog_depth);

            let mut builder = Builder::<T>::new(binary_depth, 0)?;
            let mut count = 0;

            // Fill up each subtree to its capacity.
            while count < capacity {
                match iter.next() {
                    Some(item) => {
                        builder.push(item)?;
                        count += 1;
                    }
                    None => break,
                }
            }

            if count == 0 {
                // No items left.
                break;
            }

            let (tree, _, _) = builder.finish()?;
            subtrees.push(tree);

            if count < capacity {
                // No items left and subtree is only partially filled.
                break;
            }

            // Move to the next subtree.
            prog_depth += 1;
        }

        // Assemble the `ProgressiveTree` in reverse from deepest to shallowest.
        let mut current = Self::ProgressiveZero;
        for tree in subtrees.into_iter().rev() {
            current = Self::ProgressiveNode {
                hash: RwLock::new(Hash256::ZERO),
                left: tree,
                right: Arc::new(current),
            };
        }

        Ok(current)
    }

    fn push_recursive(
        &self,
        value: T,
        current_length: usize,
        prog_depth: u32,
    ) -> Result<Self, Error> {
        match self {
            // Expand this zero into a new left node for our element.
            Self::ProgressiveZero => {
                // The `prog_depth` of the new left subtree is `prog_depth + 1`.
                let subtree_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                let mut tree_builder = Builder::<T>::new(subtree_depth, 0)?;
                tree_builder.push(value)?;
                let (new_left, _, _) = tree_builder.finish()?;

                Ok(Self::ProgressiveNode {
                    hash: RwLock::new(Hash256::ZERO),
                    left: new_left,
                    right: Arc::new(Self::ProgressiveZero),
                })
            }
            Self::ProgressiveNode {
                hash: _,
                left,
                right,
            } => {
                // Case 1: new element already fits inside the left-tree at prog_depth + 1.
                let total_capacity_at_depth = Self::total_capacity_at_depth(prog_depth + 1);
                if current_length < total_capacity_at_depth {
                    let index =
                        current_length.saturating_sub(Self::total_capacity_at_depth(prog_depth));

                    // Our left subtree can hold 4^prog_depth entries. We need to work out
                    // a 2-based depth for this sub tree, such that the subtree holds
                    // 2^subtree_depth entries.
                    let subtree_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                    let new_left = left.with_updated_leaf(index, value, subtree_depth)?;

                    // FIXME: remove assert
                    debug_assert!(matches!(**right, Self::ProgressiveZero));

                    Ok(Self::ProgressiveNode {
                        hash: RwLock::new(Hash256::ZERO),
                        left: new_left,
                        right: right.clone(),
                    })
                } else {
                    // Case 2: new element does not fit inside this left-tree: recurse to the next
                    // level on the right.
                    let new_right = right.push_recursive(value, current_length, prog_depth + 1)?;

                    Ok(Self::ProgressiveNode {
                        hash: RwLock::new(Hash256::ZERO),
                        left: left.clone(),
                        right: Arc::new(new_right),
                    })
                }
            }
        }
    }

    pub fn push(&self, value: T, current_length: usize) -> Result<Self, Error> {
        self.push_recursive(value, current_length, 0)
    }

    /// Create an iterator over all elements in the progressive tree.
    ///
    /// The iterator traverses elements in order by visiting each binary subtree
    /// (left child) at increasing progressive depths:
    /// 1. All elements in the left child at the root level
    /// 2. All elements in the left child of the first right node
    /// 3. All elements in the left child of the second right node
    ///
    /// And so on, following the progressive tree structure as defined in EIP-7916.
    pub fn iter(&self, length: usize) -> ProgressiveTreeIter<'_, T> {
        ProgressiveTreeIter::new(self, length)
    }
}

impl<T: Value + Send + Sync> ProgressiveTree<T> {
    pub fn tree_hash(&self) -> Hash256 {
        match self {
            Self::ProgressiveZero => Hash256::ZERO,
            Self::ProgressiveNode { hash, left, right } => {
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

/// Iterator over elements in a progressive tree.
///
/// The iterator traverses each binary subtree (left child) in sequence by following
/// the right spine of the progressive tree structure.
#[derive(Debug)]
pub struct ProgressiveTreeIter<'a, T: Value> {
    /// Current progressive node being traversed.
    current_prog_node: Option<&'a ProgressiveTree<T>>,
    /// Current iterator over a binary subtree (Tree).
    current_iter: Option<Iter<'a, T>>,
    /// Progressive depth for calculating the next subtree depth.
    prog_depth: u32,
    /// Total number of elements to iterate.
    length: usize,
    /// Number of elements already yielded.
    yielded: usize,
}

impl<'a, T: Value> ProgressiveTreeIter<'a, T> {
    fn new(root: &'a ProgressiveTree<T>, length: usize) -> Self {
        let mut iter = Self {
            current_prog_node: Some(root),
            current_iter: None,
            prog_depth: 0,
            length,
            yielded: 0,
        };

        // Initialize by setting up the iterator for the first left child
        iter.advance_to_next_subtree();
        iter
    }

    /// Advance to the next binary subtree by moving to the right child and
    /// setting up an iterator for its left child.
    fn advance_to_next_subtree(&mut self) {
        match self.current_prog_node {
            None | Some(ProgressiveTree::ProgressiveZero) => {
                // No more subtrees
                self.current_iter = None;
                self.current_prog_node = None;
            }
            Some(ProgressiveTree::ProgressiveNode { left, right, .. }) => {
                self.prog_depth += 1;

                // Calculate the depth and length for this binary subtree
                let binary_depth =
                    ProgressiveTree::<T>::prog_depth_to_binary_depth(self.prog_depth);
                let remaining = self.length.saturating_sub(self.yielded);
                let capacity = ProgressiveTree::<T>::capacity_at_depth(self.prog_depth);
                let subtree_length = remaining.min(capacity);

                // Create an iterator for the left subtree
                self.current_iter = Some(Iter::from_index(
                    0,
                    left,
                    binary_depth,
                    Length(subtree_length),
                ));

                // Move to the right child for the next iteration
                self.current_prog_node = Some(right);
            }
        }
    }
}

impl<'a, T: Value> Iterator for ProgressiveTreeIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Try to get the next item from the current binary tree iterator
            if let Some(iter) = &mut self.current_iter
                && let Some(value) = iter.next()
            {
                self.yielded += 1;
                return Some(value);
            }

            // Current subtree exhausted, move to the next one
            if self.current_prog_node.is_some() {
                self.advance_to_next_subtree();
            } else {
                // No more subtrees to iterate
                return None;
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.saturating_sub(self.yielded);
        (remaining, Some(remaining))
    }
}

impl<T: Value> ExactSizeIterator for ProgressiveTreeIter<'_, T> {}
