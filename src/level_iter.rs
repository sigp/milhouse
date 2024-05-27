use crate::{
    utils::{compute_level, opt_packing_depth, opt_packing_factor, Length},
    Arc, PackedLeaf, Tree, Value,
};

/// Iterator over the internal nodes at a given `depth` (level) in a tree.
#[derive(Debug)]
pub struct LevelIter<'a, T: Value> {
    /// Stack of tree nodes corresponding to the current position.
    stack: Vec<&'a Arc<Tree<T>>>,
    /// The list index corresponding to the current position (next element to be yielded).
    index: usize,
    /// The level of the tree being iterated.
    level: usize,
    /// The `depth` of the root tree.
    full_depth: usize,
    /// Cached packing factor to avoid re-calculating `opt_packing_factor`.
    ///
    /// Initialised to 0 if `T` is not packed.
    packing_factor: usize,
    /// Cached packing depth to avoid re-calculating `opt_packing_depth`.
    packing_depth: usize,
    /// Number of elements in the list being iterated.
    length: Length,
}

/// Item yielded by a `LevelIter`.
///
/// If we are iterating an internal level, then all `Internal` nodes `Arc` pointers will be
/// returned. Otherwise if we are iterating at the leaf level over packed leaves, references to
/// leaves will be returned.
#[derive(Debug)]
pub enum LevelNode<'a, T: Value> {
    Internal(&'a Arc<Tree<T>>),
    PackedLeaf(&'a T),
}

impl<'a, T: Value> LevelIter<'a, T> {
    pub fn from_index(index: usize, root: &'a Arc<Tree<T>>, depth: usize, length: Length) -> Self {
        let mut stack = Vec::with_capacity(depth);
        stack.push(root);

        let packing_factor = opt_packing_factor::<T>().unwrap_or(0);
        let packing_depth = opt_packing_depth::<T>().unwrap_or(0);

        let level = compute_level(index, depth, packing_depth);

        LevelIter {
            stack,
            index,
            level,
            full_depth: depth,
            packing_factor,
            packing_depth,
            length,
        }
    }
}

impl<'a, T: Value> Iterator for LevelIter<'a, T> {
    type Item = LevelNode<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.length.as_usize() {
            return None;
        }

        let node: &'a Arc<Tree<T>> = *self.stack.last()?;
        match node.as_ref() {
            Tree::Zero(_) => None,
            Tree::Leaf(_) => {
                let result = Some(LevelNode::Internal(node));

                // If we are iterating leaves then the level must be 0.
                debug_assert_eq!(self.level, 0);
                self.index += 1;

                // Backtrack to the parent node of the next subtree
                for _ in 0..=self.index.trailing_zeros() {
                    self.stack.pop();
                }

                result
            }
            Tree::PackedLeaf(PackedLeaf { values, .. }) => {
                let node_depth = self.full_depth + self.packing_depth - self.stack.len() + 1;

                if node_depth == self.level {
                    let result = Some(LevelNode::Internal(node));

                    // Jump to the next index on the same level.
                    self.index += 1 << self.level;

                    let trailing_zeros = self.index.trailing_zeros() as usize;
                    debug_assert!(trailing_zeros >= self.level);
                    let to_pop = trailing_zeros.saturating_add(1).saturating_sub(self.level);

                    // Backtrack to the parent node of the next subtree
                    for _ in 0..to_pop {
                        self.stack.pop();
                    }

                    return result;
                }

                let sub_index = self.index % self.packing_factor;
                let result = values.get(sub_index).map(LevelNode::PackedLeaf);

                // If we are iterating leaves then the level must be 0.
                debug_assert_eq!(self.level, 0);
                self.index += 1;

                // Reached end of chunk
                if sub_index + 1 == self.packing_factor {
                    let to_pop = self
                        .index
                        .trailing_zeros()
                        .checked_sub(self.packing_depth as u32)
                        .expect("index should have at least `packing_depth` trailing zeroes");

                    for _ in 0..=to_pop {
                        self.stack.pop();
                    }
                }

                result
            }
            Tree::Node { left, right, .. } => {
                let child_depth = self.full_depth + self.packing_depth - self.stack.len();
                let node_depth = child_depth + 1;

                if node_depth == self.level {
                    let result = Some(LevelNode::Internal(node));

                    // Jump to the next index on the same level.
                    self.index += 1 << self.level;

                    let trailing_zeros = self.index.trailing_zeros() as usize;
                    debug_assert!(trailing_zeros >= self.level);
                    let to_pop = trailing_zeros.saturating_add(1).saturating_sub(self.level);

                    // Backtrack to the parent node of the next subtree
                    for _ in 0..to_pop {
                        self.stack.pop();
                    }

                    result
                } else if (self.index >> child_depth) & 1 == 0 {
                    // Go left
                    self.stack.push(left);
                    self.next()
                } else {
                    // Go right
                    self.stack.push(right);
                    self.next()
                }
            }
        }
    }
}
