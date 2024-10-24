use crate::{Arc, List, Tree, UpdateMap, Value, Vector};
use std::collections::HashMap;
use typenum::Unsigned;

pub trait MemorySize {
    /// The memory address of this item.
    fn self_pointer(&self) -> usize;

    /// Subtrees (Arcs) for this type's fields that consume memory.
    fn subtrees(&self) -> Vec<&dyn MemorySize>;

    /// Memory consumed by this type's non-recursive fields.
    fn intrinsic_size(&self) -> usize;
}

/// Memory usage (RAM) analysis for Milhouse data structures.
#[derive(Default)]
pub struct MemoryTracker {
    // Map from pointer to size of subtree referenced by that pointer.
    subtree_sizes: HashMap<usize, usize>,
}

#[derive(Debug)]
pub struct ItemStats {
    /// Total size of this item ignorning structural sharing.
    pub total_size: usize,
    /// Amount of memory used by this item in addition to memory that was already tracked.
    pub differential_size: usize,
}

impl MemoryTracker {
    pub fn track_item<T: MemorySize + ?Sized>(&mut self, item: &T) -> ItemStats {
        let ptr = item.self_pointer();

        // If this item is already tracked, then its differential size is 0.
        if let Some(&total_size) = self.subtree_sizes.get(&ptr) {
            return ItemStats {
                total_size,
                differential_size: 0,
            };
        }

        // Otherwise, calculate the intrinsic size of this item, and recurse into its subtrees.
        let intrinsic_size = item.intrinsic_size();

        let subtrees = item.subtrees();

        let mut total_size = intrinsic_size;
        let mut differential_size = intrinsic_size;

        for subtree in subtrees {
            let subtree_stats = self.track_item(subtree);
            total_size += subtree_stats.total_size;
            differential_size += subtree_stats.differential_size;
        }

        self.subtree_sizes.insert(ptr, total_size);

        ItemStats {
            total_size,
            differential_size,
        }
    }
}

impl<T: Value> MemorySize for Arc<Tree<T>> {
    fn self_pointer(&self) -> usize {
        self.as_ptr() as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        match &**self {
            Tree::Leaf(_) | Tree::PackedLeaf(_) | Tree::Zero(_) => vec![],
            Tree::Node { left, right, .. } => {
                vec![left, right]
            }
        }
    }

    fn intrinsic_size(&self) -> usize {
        std::mem::size_of::<Tree<T>>()
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> MemorySize for List<T, N, U> {
    fn self_pointer(&self) -> usize {
        self as *const _ as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        vec![&self.interface.backing.tree]
    }

    fn intrinsic_size(&self) -> usize {
        // This approximates the size of the UpdateMap, and assumes that `T` is not recursive.
        // We could probably add a `T: MemorySize` bound? In most practical cases the update map
        // should be empty anyway.
        std::mem::size_of::<Self>() + self.interface.updates.len() * std::mem::size_of::<T>()
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> MemorySize for Vector<T, N, U> {
    fn self_pointer(&self) -> usize {
        self as *const _ as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        vec![&self.interface.backing.tree]
    }

    fn intrinsic_size(&self) -> usize {
        // This approximates the size of the UpdateMap, and assumes that `T` is not recursive.
        // We could probably add a `T: MemorySize` bound? In most practical cases the update map
        // should be empty anyway.
        std::mem::size_of::<Self>() + self.interface.updates.len() * std::mem::size_of::<T>()
    }
}
