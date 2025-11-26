use crate::{Arc, Error, Tree, Value, builder::Builder, iter::Iter, utils::{Length, opt_packing_factor}};
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
                PROG_TREE_BINARY_SCALE * prog_depth_minus_one as usize
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

    /// Create an iterator over all elements in the progressive tree.
    ///
    /// The iterator traverses elements in order:
    /// 1. All elements in the first right child (prog_depth=1)
    /// 2. All elements in the right child of the first left child (prog_depth=2)
    /// 3. All elements in the right child of the second left child (prog_depth=3)
    ///
    /// And so on, following the progressive tree structure.
    pub fn iter(&self, length: usize) -> ProgTreeIter<'_, T> {
        ProgTreeIter::new(self, length)
    }
}

/// Iterator over elements in a progressive tree.
///
/// The iterator maintains a stack of `ProgNode`s to continue iteration after each
/// binary subtree (right child) is exhausted.
#[derive(Debug)]
pub struct ProgTreeIter<'a, T: Value> {
    /// Stack of progressive nodes to visit (their right children).
    prog_stack: Vec<&'a ProgTree<T>>,
    /// Current iterator over a binary subtree (Tree).
    current_iter: Option<Iter<'a, T>>,
    /// Progressive depth for calculating the next subtree depth.
    prog_depth: u32,
    /// Total number of elements to iterate.
    length: usize,
    /// Number of elements already yielded.
    yielded: usize,
}

impl<'a, T: Value> ProgTreeIter<'a, T> {
    fn new(root: &'a ProgTree<T>, length: usize) -> Self {
        let mut iter = Self {
            prog_stack: Vec::new(),
            current_iter: None,
            prog_depth: 0,
            length,
            yielded: 0,
        };

        // Initialize by traversing to the first right child
        iter.advance_to_next_subtree(root);
        iter
    }

    /// Advance to the next binary subtree by traversing down the left spine
    /// and setting up an iterator for the right child.
    fn advance_to_next_subtree(&mut self, node: &'a ProgTree<T>) {
        match node {
            ProgTree::ProgZero => {
                // No more subtrees
                self.current_iter = None;
            }
            ProgTree::ProgNode { left, right, .. } => {
                self.prog_depth += 1;

                // Calculate the depth and length for this binary subtree
                let binary_depth = ProgTree::<T>::prog_depth_to_binary_depth(self.prog_depth);
                let remaining = self.length.saturating_sub(self.yielded);
                let capacity = ProgTree::<T>::capacity_at_depth(self.prog_depth);
                let subtree_length = remaining.min(capacity);

                // Create an iterator for the right subtree
                self.current_iter = Some(Iter::from_index(
                    0,
                    right,
                    binary_depth,
                    Length(subtree_length),
                ));

                // Push the left child to continue later
                self.prog_stack.push(left);
            }
        }
    }
}

impl<'a, T: Value> Iterator for ProgTreeIter<'a, T> {
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
            if let Some(next_prog_node) = self.prog_stack.pop() {
                self.advance_to_next_subtree(next_prog_node);
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

impl<T: Value> ExactSizeIterator for ProgTreeIter<'_, T> {}
