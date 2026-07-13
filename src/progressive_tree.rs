use crate::{
    Arc, Error, Tree, UpdateMap, Value,
    builder::Builder,
    iter::Iter,
    tree::RebaseAction,
    utils::{Length, opt_packing_depth, opt_packing_factor, updated_length},
};
use educe::Educe;
use ethereum_hashing::hash32_concat;
use parking_lot::RwLock;
use std::ops::ControlFlow;
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
                // This is the depth of the binary subtree counted in nodes above its (packed)
                // leaves, i.e. the packing depth is deliberately excluded. `Tree`/`Builder` add
                // the packing depth back internally, and `capacity_at_depth` already multiplies by
                // the packing factor, so the chunk count `2^binary_depth` lines up with the element
                // capacity `2^binary_depth * packing_factor`. Subtracting the packing depth here
                // would double-count it.
                PROG_TREE_BINARY_SCALE * prog_depth_minus_one as usize
            }
        }
    }

    /// Build a `ProgressiveTree` efficiently from an iterator.
    /// Only creates one `Builder` per subtree.
    pub fn build_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        Ok(Self::build_from_iter_with_len(iter)?.0)
    }

    /// Like [`Self::build_from_iter`], but also returns the number of items consumed so callers do
    /// not need to count the iterator separately.
    pub(crate) fn build_from_iter_with_len(
        iter: impl IntoIterator<Item = T>,
    ) -> Result<(Self, usize), Error> {
        let mut iter = iter.into_iter();
        let mut subtrees: Vec<Arc<Tree<T>>> = Vec::new();
        let mut prog_depth = 1u32;
        let mut length = 0;

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
            length += count;

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

        Ok((current, length))
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
                // The new element is the first leaf of a fresh binary subtree at `prog_depth + 1`.
                // Setting it on a zero subtree yields the same tree as building one with `Builder`,
                // without allocating the builder.
                let subtree_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                let new_left =
                    Tree::zero(subtree_depth).with_updated_leaf(0, value, subtree_depth)?;

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

                    // Invariant: a list has no gaps, so if the append still fits in this level's
                    // left subtree then no deeper level has been opened yet.
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

    /// Create an iterator over the elements starting at `index`.
    ///
    /// Seeks to the right binary subtree using the spine geometry (rather than discarding elements
    /// one at a time), so the cost is logarithmic in `index`.
    pub fn iter_from(&self, index: usize, length: usize) -> ProgressiveTreeIter<'_, T> {
        ProgressiveTreeIter::from_index(self, index, length)
    }

    pub fn get_recursive(&self, index: usize, prog_depth: u32) -> Option<&T> {
        match self {
            Self::ProgressiveZero => None,
            Self::ProgressiveNode { left, right, .. } => {
                let total_capacity = Self::total_capacity_at_depth(prog_depth + 1);
                if index < total_capacity {
                    // Index is in the left subtree (binary tree).
                    let subtree_index =
                        index.saturating_sub(Self::total_capacity_at_depth(prog_depth));
                    let binary_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                    let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
                    left.get_recursive(subtree_index, binary_depth, packing_depth)
                } else {
                    // Index is in the right subtree (progressive tree).
                    right.get_recursive(index, prog_depth + 1)
                }
            }
        }
    }

    /// Create a new tree where the `index`th leaf is set to `value`.
    ///
    /// If `index == current_length` the value is appended (equivalent to `push`). Updating any
    /// index `> current_length` is an error, as it would leave a gap in the list.
    pub fn with_updated_leaf(
        &self,
        index: usize,
        value: T,
        current_length: usize,
    ) -> Result<Self, Error> {
        if index < current_length {
            self.replace_recursive(index, value, 0)
        } else if index == current_length {
            self.push_recursive(value, current_length, 0)
        } else {
            Err(Error::OutOfBoundsUpdate {
                index,
                len: current_length,
            })
        }
    }

    /// Apply a whole batch of updates to the tree in a single walk of the progressive spine.
    ///
    /// This is the batched equivalent of calling [`Self::with_updated_leaf`] once per update in
    /// ascending index order: it produces an identical tree (and therefore an identical root) but
    /// only walks the spine once. At each spine level the pending updates are partitioned into
    /// those landing in this node's binary (left) subtree, which are delegated to the already
    /// batched [`Tree::with_updated_leaves`], and those landing further right, which are handled by
    /// recursing into `right`. Appends are supported and grow the spine just like `push`.
    ///
    /// `current_length` is the length of the list before the updates are applied.
    pub fn with_updated_leaves<U: UpdateMap<T>>(
        &self,
        updates: &U,
        current_length: usize,
    ) -> Result<Self, Error> {
        let new_length = updated_length(Length(current_length), updates).as_usize();

        // The largest updated index tells each spine level whether anything lands at or beyond the
        // next subtree with a single O(1) comparison, instead of re-scanning the tail at every
        // level. If the batch grew the list then appends are contiguous and the largest index is
        // exactly `new_length - 1`; otherwise (a pure-replace batch) we find it in one forward pass.
        // NOTE: we deliberately don't use `UpdateMap::max_index` here, as `MaxMap` only tracks
        // appends (`insert`), not replaces made via `get_mut`/`get_cow`.
        let max_index = if new_length > current_length {
            Some(new_length - 1)
        } else {
            let mut max = None;
            updates.for_each_range(0, new_length, |index, _| {
                max = Some(index);
                ControlFlow::Continue(Ok::<(), Error>(()))
            })?;
            max
        };

        self.with_updated_leaves_recursive(updates, max_index, 0)
    }

    fn with_updated_leaves_recursive<U: UpdateMap<T>>(
        &self,
        updates: &U,
        max_index: Option<usize>,
        prog_depth: u32,
    ) -> Result<Self, Error> {
        // Global index range `[subtree_start, subtree_end)` covered by this node's binary (left)
        // subtree.
        let subtree_start = Self::total_capacity_at_depth(prog_depth);
        let subtree_end = Self::total_capacity_at_depth(prog_depth + 1);
        let binary_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);

        match self {
            Self::ProgressiveZero => {
                if !Self::has_updates_in_range(updates, subtree_start, subtree_end) {
                    // No appended element opens this spine level (and, since a list has no gaps,
                    // nothing lands further right either).
                    return Ok(Self::ProgressiveZero);
                }

                // Grow a new spine level: build the binary subtree from empty, applying the updates
                // that land in it directly from the original map (shifted by `subtree_start`)
                // rather than copying them into a temporary map.
                let zero = Tree::zero(binary_depth);
                let new_left =
                    zero.with_updated_leaves(updates, 0, subtree_start, binary_depth, None)?;

                let new_right = if max_index.is_some_and(|max| max >= subtree_end) {
                    Arc::new(Self::ProgressiveZero.with_updated_leaves_recursive(
                        updates,
                        max_index,
                        prog_depth + 1,
                    )?)
                } else {
                    Arc::new(Self::ProgressiveZero)
                };

                Ok(Self::ProgressiveNode {
                    hash: RwLock::new(Hash256::ZERO),
                    left: new_left,
                    right: new_right,
                })
            }
            Self::ProgressiveNode { left, right, .. } => {
                // Apply the updates landing in this node's binary subtree, leaving it untouched if
                // none do (its existing leaves are preserved either way).
                let new_left = if Self::has_updates_in_range(updates, subtree_start, subtree_end) {
                    // Apply the updates landing in this subtree directly from the original map,
                    // shifted by `subtree_start`, instead of collecting them into a temporary map.
                    left.with_updated_leaves(updates, 0, subtree_start, binary_depth, None)?
                } else {
                    left.clone()
                };

                // Recurse for updates landing further right, again skipping the work if there are
                // none. `max_index >= subtree_end` is exactly "some update lands at or beyond the
                // next subtree", since every update index is `<= max_index`.
                let new_right = if max_index.is_some_and(|max| max >= subtree_end) {
                    Arc::new(right.with_updated_leaves_recursive(
                        updates,
                        max_index,
                        prog_depth + 1,
                    )?)
                } else {
                    right.clone()
                };

                Ok(Self::ProgressiveNode {
                    hash: RwLock::new(Hash256::ZERO),
                    left: new_left,
                    right: new_right,
                })
            }
        }
    }

    /// Whether `updates` contains any index in `[start, end)`.
    fn has_updates_in_range<U: UpdateMap<T>>(updates: &U, start: usize, end: usize) -> bool {
        if start >= end {
            return false;
        }
        let mut found = false;
        let _: Result<(), Error> = updates.for_each_range(start, end, |_, _| {
            found = true;
            ControlFlow::Break(())
        });
        found
    }

    /// Replace the value at an *existing* `index`, leaving the list length unchanged.
    ///
    /// Routes to the binary subtree containing `index` using the same geometry as
    /// `get_recursive`/`push_recursive`, then delegates the in-subtree update to `Tree`.
    fn replace_recursive(&self, index: usize, value: T, prog_depth: u32) -> Result<Self, Error> {
        match self {
            Self::ProgressiveZero => Err(Error::OutOfBoundsUpdate { index, len: 0 }),
            Self::ProgressiveNode { left, right, .. } => {
                let total_capacity = Self::total_capacity_at_depth(prog_depth + 1);
                if index < total_capacity {
                    // Index lies in this node's binary (left) subtree.
                    let subtree_index =
                        index.saturating_sub(Self::total_capacity_at_depth(prog_depth));
                    let binary_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                    let new_left = left.with_updated_leaf(subtree_index, value, binary_depth)?;

                    Ok(Self::ProgressiveNode {
                        hash: RwLock::new(Hash256::ZERO),
                        left: new_left,
                        right: right.clone(),
                    })
                } else {
                    // Recurse into the right (progressive) subtree.
                    let new_right = right.replace_recursive(index, value, prog_depth + 1)?;

                    Ok(Self::ProgressiveNode {
                        hash: RwLock::new(Hash256::ZERO),
                        left: left.clone(),
                        right: Arc::new(new_right),
                    })
                }
            }
        }
    }

    /// Rebase `orig` onto `base`, exploiting structural sharing between equal subtrees to reduce
    /// memory usage. The logical contents and `tree_hash` of `orig` are unchanged; only `Arc`
    /// pointers are shared with `base` where subtrees are equal.
    pub fn rebase_on(
        orig: &Arc<Self>,
        base: &Arc<Self>,
        orig_length: usize,
        base_length: usize,
    ) -> Result<Arc<Self>, Error> {
        Self::rebase_on_recursive(orig, base, orig_length, base_length, 0)
    }

    fn rebase_on_recursive(
        orig: &Arc<Self>,
        base: &Arc<Self>,
        orig_length: usize,
        base_length: usize,
        prog_depth: u32,
    ) -> Result<Arc<Self>, Error> {
        if Arc::ptr_eq(orig, base) {
            return Ok(base.clone());
        }
        match (&**orig, &**base) {
            // `orig` is empty here, or `base` has nothing to share. Keep `orig` as-is.
            (Self::ProgressiveZero, _) | (Self::ProgressiveNode { .. }, Self::ProgressiveZero) => {
                Ok(orig.clone())
            }
            (
                Self::ProgressiveNode {
                    hash: orig_hash,
                    left: orig_left,
                    right: orig_right,
                },
                Self::ProgressiveNode {
                    left: base_left,
                    right: base_right,
                    ..
                },
            ) => {
                let subtree_start = Self::total_capacity_at_depth(prog_depth);
                let subtree_capacity = Self::capacity_at_depth(prog_depth + 1);
                let binary_depth = Self::prog_depth_to_binary_depth(prog_depth + 1);
                let packing_depth = opt_packing_depth::<T>().unwrap_or(0);

                let orig_left_len = orig_length
                    .saturating_sub(subtree_start)
                    .min(subtree_capacity);
                let base_left_len = base_length
                    .saturating_sub(subtree_start)
                    .min(subtree_capacity);

                // Rebase the binary (left) subtree using the existing `Tree` machinery.
                let new_left = match Tree::rebase_on(
                    orig_left,
                    base_left,
                    Some((Length(orig_left_len), Length(base_left_len))),
                    binary_depth + packing_depth,
                )? {
                    RebaseAction::EqualReplace(replacement) => replacement.clone(),
                    RebaseAction::NotEqualReplace(replacement) => replacement,
                    RebaseAction::EqualNoop | RebaseAction::NotEqualNoop => orig_left.clone(),
                };

                // Rebase the progressive (right) subtree.
                let new_right = Self::rebase_on_recursive(
                    orig_right,
                    base_right,
                    orig_length,
                    base_length,
                    prog_depth + 1,
                )?;

                // Avoid allocating a new node if nothing changed.
                if Arc::ptr_eq(&new_left, orig_left) && Arc::ptr_eq(&new_right, orig_right) {
                    Ok(orig.clone())
                } else {
                    Ok(Arc::new(Self::ProgressiveNode {
                        hash: RwLock::new(*orig_hash.read()),
                        left: new_left,
                        right: new_right,
                    }))
                }
            }
        }
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
        // Starting from index 0 is just the general seek with no elements skipped.
        Self::from_index(root, 0, length)
    }

    /// Create an iterator positioned at `start_index`.
    ///
    /// Walks the right spine to the binary subtree that holds `start_index` and seeks within it,
    /// rather than yielding and discarding the preceding elements.
    fn from_index(root: &'a ProgressiveTree<T>, start_index: usize, length: usize) -> Self {
        let mut iter = Self {
            current_prog_node: Some(root),
            current_iter: None,
            prog_depth: 0,
            length,
            yielded: start_index,
        };
        iter.seek_to_subtree(start_index);
        iter
    }

    /// Skip whole binary subtrees along the right spine until the one containing `start_index` is
    /// reached, then set up its inner iterator at the matching local offset.
    fn seek_to_subtree(&mut self, start_index: usize) {
        loop {
            match self.current_prog_node {
                None | Some(ProgressiveTree::ProgressiveZero) => {
                    self.current_iter = None;
                    self.current_prog_node = None;
                    return;
                }
                Some(ProgressiveTree::ProgressiveNode { left, right, .. }) => {
                    // This node's binary subtree is at progressive depth `prog_depth + 1` and
                    // covers the global index range `[subtree_start, subtree_end)`.
                    let next_depth = self.prog_depth + 1;
                    let subtree_start =
                        ProgressiveTree::<T>::total_capacity_at_depth(self.prog_depth);
                    let subtree_end = ProgressiveTree::<T>::total_capacity_at_depth(next_depth);
                    self.prog_depth = next_depth;

                    if start_index < subtree_end {
                        // The target lives in this subtree; seek to it and stop.
                        let binary_depth =
                            ProgressiveTree::<T>::prog_depth_to_binary_depth(next_depth);
                        let capacity = ProgressiveTree::<T>::capacity_at_depth(next_depth);
                        let remaining = self.length.saturating_sub(subtree_start);
                        let subtree_length = remaining.min(capacity);
                        let local_index = start_index - subtree_start;

                        self.current_iter = Some(Iter::from_index(
                            local_index,
                            left,
                            binary_depth,
                            Length(subtree_length),
                        ));
                        self.current_prog_node = Some(right);
                        return;
                    }

                    // `start_index` is past this subtree; skip it without building an iterator.
                    self.current_prog_node = Some(right);
                }
            }
        }
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
