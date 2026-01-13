use crate::level_iter::LevelIter;
use crate::update_map::UpdateMap;
use crate::utils::{Length, updated_length};
use crate::{
    Arc, Cow, Error, Tree, Value,
    interface_iter::{InterfaceIter, InterfaceIterCow},
    iter::Iter,
};
use std::collections::BTreeMap;
use std::marker::PhantomData;
use tree_hash::Hash256;

pub trait ImmList<T: Value> {
    fn get(&self, idx: usize) -> Option<&T>;

    fn len(&self) -> Length;

    fn is_empty(&self) -> bool {
        self.len().as_usize() == 0
    }

    fn iter_from(&self, index: usize) -> Iter<'_, T>;

    fn level_iter_from(&self, index: usize) -> LevelIter<'_, T>;

    fn tree(&self) -> &Arc<Tree<T>>;

    fn depth(&self) -> usize;

    fn packing_depth(&self) -> usize;
}

pub trait MutList<T: Value>: ImmList<T> {
    fn validate_push(current_len: usize) -> Result<(), Error>;
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error>;
    fn update<U: UpdateMap<T>>(
        &mut self,
        updates: U,
        hash_updates: Option<BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<(), Error>;
}

#[derive(Debug, PartialEq, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Interface<T, B, U>
where
    T: Value,
    B: MutList<T>,
    U: UpdateMap<T>,
{
    pub(crate) backing: B,
    pub(crate) updates: U,
    pub(crate) _phantom: PhantomData<T>,
}

impl<T, B, U> Interface<T, B, U>
where
    T: Value,
    B: MutList<T>,
    U: UpdateMap<T>,
{
    pub fn new(backing: B) -> Self {
        Self {
            backing,
            updates: U::default(),
            _phantom: PhantomData,
        }
    }

    pub fn get(&self, idx: usize) -> Option<&T> {
        self.updates.get(idx).or_else(|| self.backing.get(idx))
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        self.updates
            .get_mut_with(idx, |idx| self.backing.get(idx).cloned())
    }

    pub fn get_cow(&mut self, index: usize) -> Option<Cow<'_, T>> {
        self.updates
            .get_cow_with(index, |idx| self.backing.get(idx))
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        let index = self.len();
        B::validate_push(index)?;
        self.updates.insert(index, value);

        Ok(())
    }

    pub fn apply_updates(&mut self) -> Result<(), Error> {
        if !self.updates.is_empty() {
            let updates = std::mem::take(&mut self.updates);
            self.backing.update(updates, None)
        } else {
            Ok(())
        }
    }

    pub fn has_pending_updates(&self) -> bool {
        !self.updates.is_empty()
    }

    pub fn iter(&self) -> InterfaceIter<'_, T, U> {
        self.iter_from(0)
    }

    pub fn iter_from(&self, index: usize) -> InterfaceIter<'_, T, U> {
        InterfaceIter {
            tree_iter: self.backing.iter_from(index),
            updates: &self.updates,
            index,
            length: self.len(),
        }
    }

    pub fn iter_cow(&mut self) -> InterfaceIterCow<'_, T, U> {
        self.iter_cow_from(0)
    }

    pub fn iter_cow_from(&mut self, index: usize) -> InterfaceIterCow<'_, T, U> {
        InterfaceIterCow {
            tree_iter: self.backing.iter_from(index),
            updates: &mut self.updates,
            index,
        }
    }

    pub fn level_iter_from(&self, index: usize) -> Result<LevelIter<'_, T>, Error> {
        if self.has_pending_updates() {
            Err(Error::LevelIterPendingUpdates)
        } else {
            Ok(self.backing.level_iter_from(index))
        }
    }

    pub fn len(&self) -> usize {
        updated_length(self.backing.len(), &self.updates).as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn bulk_update(&mut self, updates: U) -> Result<(), Error> {
        if !self.updates.is_empty() {
            return Err(Error::BulkUpdateUnclean);
        }
        self.updates = updates;
        Ok(())
    }

    /// Compute the tree hash root, accounting for pending updates.
    ///
    /// This method computes the tree hash without applying pending updates to the backing tree.
    /// It recursively traverses the tree, using values from pending updates where they exist,
    /// and cached hashes from the tree where they don't.
    pub fn tree_hash_root(&self, full_length: usize) -> Hash256
    where
        T: Send + Sync,
        B: ImmList<T>,
    {
        let tree = self.backing.tree();
        let depth = self.backing.depth();
        let packing_depth = self.backing.packing_depth();
        
        if self.updates.is_empty() {
            // No pending updates, just use the cached tree hash
            tree.tree_hash()
        } else {
            // Compute tree hash while considering pending updates
            self.tree_hash_recursive(tree, &self.updates, 0, depth, packing_depth, full_length)
        }
    }

    /// Recursively compute tree hash for a subtree, considering pending updates.
    fn tree_hash_recursive(
        &self,
        node: &Tree<T>,
        updates: &U,
        prefix: usize,
        depth: usize,
        packing_depth: usize,
        full_length: usize,
    ) -> Hash256
    where
        T: Send + Sync,
    {
        use crate::tree::Tree;
        use ethereum_hashing::{ZERO_HASHES, hash32_concat};
        use std::ops::ControlFlow;

        match node {
            Tree::Leaf(leaf) if depth == 0 => {
                // Check if this leaf has a pending update
                if let Some(updated_value) = updates.get(prefix) {
                    updated_value.tree_hash_root()
                } else {
                    // Use cached hash if available, otherwise compute
                    let read_lock = leaf.hash.read();
                    let existing_hash = *read_lock;
                    drop(read_lock);
                    
                    if !existing_hash.is_zero() {
                        existing_hash
                    } else {
                        leaf.value.tree_hash_root()
                    }
                }
            }
            Tree::PackedLeaf(packed_leaf) if depth == 0 => {
                // Check if any values in this packed leaf have pending updates
                let mut has_updates = false;
                let packing_factor = T::tree_hash_packing_factor();
                for i in 0..packing_factor {
                    let index = prefix + i;
                    if index >= full_length {
                        break;
                    }
                    if updates.get(index).is_some() {
                        has_updates = true;
                        break;
                    }
                }

                if has_updates {
                    // Need to recompute hash with updated values
                    let mut values = packed_leaf.values.clone();
                    for i in 0..packing_factor {
                        let index = prefix + i;
                        if index >= full_length {
                            break;
                        }
                        if let Some(updated_value) = updates.get(index) {
                            if i < values.len() {
                                values[i] = updated_value.clone();
                            } else {
                                values.push(updated_value.clone());
                            }
                        }
                    }
                    // Compute tree hash for packed values
                    crate::packed_leaf::PackedLeaf { values, hash: parking_lot::RwLock::new(Hash256::ZERO) }.tree_hash()
                } else {
                    // No updates, use cached hash
                    packed_leaf.tree_hash()
                }
            }
            Tree::Zero(zero_depth) if *zero_depth == depth => {
                Hash256::from(ZERO_HASHES[depth])
            }
            Tree::Node { hash, left, right } if depth > 0 => {
                let new_depth = depth - 1;
                let left_prefix = prefix;
                let right_prefix = prefix | (1 << (new_depth + packing_depth));
                let right_subtree_end = prefix + (1 << (depth + packing_depth));

                // Check if there are updates in left or right subtrees
                let mut has_left_updates = false;
                updates.for_each_range(left_prefix, right_prefix, |_, _| {
                    has_left_updates = true;
                    ControlFlow::<(), Result<(), Error>>::Break(())
                }).ok();
                
                let mut has_right_updates = false;
                updates.for_each_range(right_prefix, right_subtree_end, |_, _| {
                    has_right_updates = true;
                    ControlFlow::<(), Result<(), Error>>::Break(())
                }).ok();

                if !has_left_updates && !has_right_updates {
                    // No updates in this subtree, use cached hash if available
                    let read_lock = hash.read();
                    let existing_hash = *read_lock;
                    drop(read_lock);
                    
                    if !existing_hash.is_zero() {
                        return existing_hash;
                    }
                }

                // Compute hashes for left and right subtrees
                let left_hash = if has_left_updates {
                    self.tree_hash_recursive(left, updates, left_prefix, new_depth, packing_depth, full_length)
                } else {
                    left.tree_hash()
                };

                let right_hash = if has_right_updates {
                    self.tree_hash_recursive(right, updates, right_prefix, new_depth, packing_depth, full_length)
                } else {
                    right.tree_hash()
                };

                Hash256::from(hash32_concat(left_hash.as_slice(), right_hash.as_slice()))
            }
            _ => {
                // Fallback to regular tree hash for unexpected cases
                node.tree_hash()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::List;
    use typenum::U8;

    #[test]
    fn basic_mutation() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3, 4]).unwrap();

        let x = list.get_mut(0).unwrap();
        assert_eq!(*x, 1);
        *x = 11;

        let y = list.get_mut(0).unwrap();
        assert_eq!(*y, 11);

        // Applying the changes should persist them.
        assert!(list.has_pending_updates());
        list.apply_updates().unwrap();
        assert!(!list.has_pending_updates());

        // Apply empty updates should be OK.
        list.apply_updates().unwrap();

        assert_eq!(*list.get(0).unwrap(), 11);
    }

    #[test]
    fn cow_mutate_twice() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3]).unwrap();

        let c1 = list.get_cow(0).unwrap();
        assert_eq!(*c1, 1);
        *c1.into_mut().unwrap() = 10;

        assert_eq!(*list.get(0).unwrap(), 10);

        let c2 = list.get_cow(0).unwrap();
        assert_eq!(*c2, 10);
        *c2.into_mut().unwrap() = 11;
        assert_eq!(*list.get(0).unwrap(), 11);

        assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec![11, 2, 3]);
    }

    #[test]
    fn cow_iter() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3]).unwrap();

        let mut iter = list.iter_cow();
        while let Some((index, v)) = iter.next_cow() {
            *v.into_mut().unwrap() = index as u64;
        }

        assert_eq!(list.to_vec(), vec![0, 1, 2]);
    }

    #[test]
    fn cow_iter_from() {
        let mut list = List::<u64, U8>::new(vec![1, 2, 3, 4, 5]).unwrap();

        let mut iter = list.iter_cow_from(2).unwrap();
        while let Some((index, v)) = iter.next_cow() {
            *v.into_mut().unwrap() = (index * 10) as u64;
        }

        assert_eq!(list.to_vec(), vec![1, 2, 20, 30, 40]);
    }
}
