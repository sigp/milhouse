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

/// Depth scaling between the spine and its binary subtrees: a subtree holding
/// `PROG_TREE_EXPONENT^d` chunks is a binary tree of depth `d * log2(PROG_TREE_EXPONENT)`.
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
    ///
    /// Saturates at `usize::MAX` instead of overflowing, so the capacity functions grow
    /// monotonically at every depth.
    pub fn capacity_at_depth(prog_depth: u32) -> usize {
        let capacity_pre_packing = match prog_depth.checked_sub(1) {
            None => 0u128,
            Some(depth_minus_one) => (PROG_TREE_EXPONENT as u128)
                .checked_pow(depth_minus_one)
                .unwrap_or(u128::MAX),
        };
        capacity_pre_packing
            .saturating_mul(opt_packing_factor::<T>().unwrap_or(1) as u128)
            .min(usize::MAX as u128) as usize
    }

    /// The number of values that can be stored in the whole progressive tree up to and including
    /// the layer at `prog_depth`.
    ///
    /// Saturates at `usize::MAX` like [`Self::capacity_at_depth`].
    pub fn total_capacity_at_depth(prog_depth: u32) -> usize {
        let total_capacity_pre_packing = (PROG_TREE_EXPONENT as u128)
            .checked_pow(prog_depth)
            .unwrap_or(u128::MAX)
            .saturating_sub(1)
            / (PROG_TREE_EXPONENT as u128 - 1);
        total_capacity_pre_packing
            .saturating_mul(opt_packing_factor::<T>().unwrap_or(1) as u128)
            .min(usize::MAX as u128) as usize
    }

    /// Calculate the depth for the binary subtree at `prog_depth`.
    pub fn prog_depth_to_binary_depth(prog_depth: u32) -> usize {
        match prog_depth.checked_sub(1) {
            None => 0,
            Some(prog_depth_minus_one) => {
                // This depth excludes the packing depth, which `Tree` and `Builder` add back
                // internally.
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
        let mut builder = ProgressiveTreeBuilder::new()?;
        for item in iter {
            builder.push(item)?;
        }
        builder.finish()
    }

    /// Assemble a spine from complete binary subtrees, ordered from shallowest to deepest.
    fn from_spine_subtrees(subtrees: Vec<Arc<Tree<T>>>) -> Self {
        let mut current = Self::ProgressiveZero;
        for tree in subtrees.into_iter().rev() {
            current = Self::ProgressiveNode {
                hash: RwLock::new(Hash256::ZERO),
                left: tree,
                right: Arc::new(current),
            };
        }
        current
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

    /// Apply a batch of updates to the tree in a single walk of the progressive spine.
    ///
    /// At each spine level, updates landing in this node's binary (left) subtree are applied via
    /// [`Tree::with_updated_leaves`], and updates landing further right are handled by recursing
    /// into `right`. Appends grow the spine as needed.
    ///
    /// `current_length` is the length of the list before the updates are applied.
    pub fn with_updated_leaves<U: UpdateMap<T>>(
        &self,
        updates: &U,
        current_length: usize,
    ) -> Result<Self, Error> {
        let new_length = updated_length(Length(current_length), updates).as_usize();

        // The largest updated index tells each spine level whether anything lands further right.
        // For appends it is `new_length - 1`; for a replace-only batch we find it with one scan.
        // We can't use `UpdateMap::max_index` here: `MaxMap` only tracks `insert`, not replaces
        // made via `get_mut`/`get_cow`.
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

        let has_updates = Self::has_updates_in_range(updates, subtree_start, subtree_end);

        // The children to build upon: the existing children of a node, or fresh zero subtrees when
        // growing a new spine level.
        let (left, right) = match self {
            Self::ProgressiveZero => {
                if !has_updates {
                    // No append opens this spine level, and since a list has no gaps, nothing
                    // lands further right either.
                    return Ok(Self::ProgressiveZero);
                }
                (Tree::zero(binary_depth), Arc::new(Self::ProgressiveZero))
            }
            Self::ProgressiveNode { left, right, .. } => (left.clone(), right.clone()),
        };

        // Apply the updates landing in this node's binary subtree, reading them directly from the
        // original map (shifted by `subtree_start`) instead of copying them into a temporary map.
        let new_left = if has_updates {
            left.with_updated_leaves(updates, 0, subtree_start, binary_depth, None)?
        } else {
            left
        };

        // Recurse if any update lands at or beyond the next subtree.
        let new_right = if max_index.is_some_and(|max| max >= subtree_end) {
            Arc::new(right.with_updated_leaves_recursive(updates, max_index, prog_depth + 1)?)
        } else {
            right
        };

        Ok(Self::ProgressiveNode {
            hash: RwLock::new(Hash256::ZERO),
            left: new_left,
            right: new_right,
        })
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

/// Incremental builder for a [`ProgressiveTree`], the progressive analogue of
/// [`Builder`](crate::builder::Builder).
///
/// Values are pushed one at a time; each binary spine subtree is built by a [`Builder`] and
/// finished as soon as it is full.
#[derive(Debug)]
pub(crate) struct ProgressiveTreeBuilder<T: Value> {
    /// Completed binary subtrees for the spine levels below `prog_depth`.
    subtrees: Vec<Arc<Tree<T>>>,
    /// Builder for the binary subtree at `prog_depth`.
    current: Builder<T>,
    /// Progressive depth of the subtree currently being built.
    prog_depth: u32,
    /// Element capacity of the subtree at `prog_depth`, cached so `push` does not recompute it
    /// for every element.
    capacity: usize,
    /// Number of values pushed into `current`.
    count: usize,
    /// Total number of values pushed.
    length: usize,
}

impl<T: Value> ProgressiveTreeBuilder<T> {
    pub(crate) fn new() -> Result<Self, Error> {
        Ok(Self {
            subtrees: Vec::new(),
            current: Builder::new(ProgressiveTree::<T>::prog_depth_to_binary_depth(1), 0)?,
            prog_depth: 1,
            capacity: ProgressiveTree::<T>::capacity_at_depth(1),
            count: 0,
            length: 0,
        })
    }

    pub(crate) fn push(&mut self, value: T) -> Result<(), Error> {
        if self.count == self.capacity {
            // The current subtree is full: finish it and open the next spine level.
            let binary_depth =
                ProgressiveTree::<T>::prog_depth_to_binary_depth(self.prog_depth + 1);
            let full_builder = std::mem::replace(&mut self.current, Builder::new(binary_depth, 0)?);
            let (tree, _, _) = full_builder.finish()?;
            self.subtrees.push(tree);
            self.prog_depth += 1;
            self.capacity = ProgressiveTree::<T>::capacity_at_depth(self.prog_depth);
            self.count = 0;
        }
        self.current.push(value)?;
        self.count += 1;
        self.length += 1;
        Ok(())
    }

    pub(crate) fn finish(mut self) -> Result<(ProgressiveTree<T>, usize), Error> {
        if self.count > 0 {
            let (tree, _, _) = self.current.finish()?;
            self.subtrees.push(tree);
        }
        Ok((
            ProgressiveTree::from_spine_subtrees(self.subtrees),
            self.length,
        ))
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
                    let subtree_start =
                        ProgressiveTree::<T>::total_capacity_at_depth(self.prog_depth);
                    let subtree_end =
                        ProgressiveTree::<T>::total_capacity_at_depth(self.prog_depth + 1);

                    if start_index < subtree_end {
                        // The target lives in this subtree; seek to it and stop.
                        self.enter_subtree(left, right, start_index - subtree_start);
                        return;
                    }

                    // `start_index` is past this subtree; skip it without building an iterator.
                    self.prog_depth += 1;
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
                // Sequential iteration is always positioned exactly at the start of the next
                // subtree when it advances.
                self.enter_subtree(left, right, 0);
            }
        }
    }

    /// Enter the binary subtree of the spine node at `self.prog_depth + 1`, positioning its inner
    /// iterator at `local_index`, and step the spine to `right`.
    fn enter_subtree(
        &mut self,
        left: &'a Arc<Tree<T>>,
        right: &'a ProgressiveTree<T>,
        local_index: usize,
    ) {
        self.prog_depth += 1;
        let subtree_start = ProgressiveTree::<T>::total_capacity_at_depth(self.prog_depth - 1);
        let binary_depth = ProgressiveTree::<T>::prog_depth_to_binary_depth(self.prog_depth);
        let capacity = ProgressiveTree::<T>::capacity_at_depth(self.prog_depth);

        // Truncate the subtree's iteration length when the list ends inside (or before) it.
        let remaining = self.length.saturating_sub(subtree_start);
        let subtree_length = remaining.min(capacity);

        self.current_iter = Some(Iter::from_index(
            local_index,
            left,
            binary_depth,
            Length(subtree_length),
        ));
        self.current_prog_node = Some(right);
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
