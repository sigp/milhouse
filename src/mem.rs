use crate::{Arc, List, Tree, UpdateMap, Value, Vector};
use alloy_primitives::FixedBytes;
use std::collections::HashMap;
use typenum::Unsigned;

/// Trait for types supporting memory usage tracking in a `MemoryTracker`.
pub trait MemorySize {
    /// The memory address of this item.
    fn self_pointer(&self) -> usize;

    /// Subtrees (Arcs) for this type's fields that consume memory.
    fn subtrees(&self) -> Vec<&dyn MemorySize>;

    /// Memory consumed by this type's non-recursive fields.
    fn intrinsic_size(&self) -> usize;
}

/// Memory usage (RAM) analysis for Milhouse data structures.
#[derive(Debug, Default, Clone)]
pub struct MemoryTracker {
    // Map from pointer to size of subtree referenced by that pointer.
    subtree_sizes: HashMap<usize, usize>,
    // Total size of all tracked items, accounting for de-duplication.
    total_size: usize,
}

/// The memory usage stats for a single item/value.
#[derive(Debug)]
pub struct ItemStats {
    /// Total size of this item ignoring structural sharing.
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
        self.total_size += intrinsic_size;

        ItemStats {
            total_size,
            differential_size,
        }
    }

    pub fn total_size(&self) -> usize {
        self.total_size
    }
}

impl<T: MemorySize> MemorySize for Arc<T> {
    fn self_pointer(&self) -> usize {
        self.as_ptr() as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        // Recurse into the `MemorySize` impl for `T`. Note that the type coercion here is
        // extremely important: we don't want to recurse infinitely into the `Arc<T>` impl.
        let inner: &T = self;
        vec![inner]
    }

    fn intrinsic_size(&self) -> usize {
        // Just the size of the `Arc` itself. The `T` within will be counted separately.
        std::mem::size_of::<Self>()
    }
}

impl<T: Value + MemorySize> MemorySize for Tree<T> {
    fn self_pointer(&self) -> usize {
        self as *const _ as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        match self {
            // Recurse into left and right children.
            Tree::Node { left, right, .. } => {
                vec![left, right]
            }
            // To support nested size measurements we need to punch down into the leaves.
            // Use a reference to the `Arc` for the leaf so that the `Arc`'s intrinsic size is
            // counted.
            Tree::Leaf(leaf) => {
                vec![&leaf.value]
            }
            // Packed leaves and zero subtrees cannot contain any nested pointers.
            Tree::PackedLeaf(_) | Tree::Zero(_) => vec![],
        }
    }

    fn intrinsic_size(&self) -> usize {
        let leaf_size = match self {
            // This is the Vec<T> allocated inside `PackedLeaf::values`.
            Tree::PackedLeaf(packed) => packed.values.capacity() * std::mem::size_of::<T>(),
            // The leaves and inner nodes will be visited separately so we don't need to count
            // their intrinsic size here.
            Tree::Leaf(_) | Tree::Node { .. } | Tree::Zero(..) => 0,
        };
        std::mem::size_of::<Self>() + leaf_size
    }
}

impl<T: Value + MemorySize, N: Unsigned, U: UpdateMap<T>> MemorySize for List<T, N, U> {
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

impl<T: Value + MemorySize, N: Unsigned, U: UpdateMap<T>> MemorySize for Vector<T, N, U> {
    fn self_pointer(&self) -> usize {
        self as *const _ as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        vec![&self.interface.backing.tree]
    }

    fn intrinsic_size(&self) -> usize {
        // TODO(memsize): This approximates the size of the UpdateMap, and assumes that `T` is not
        // recursive. In most practical cases the update map should be empty anyway.
        std::mem::size_of::<Self>() + self.interface.updates.len() * std::mem::size_of::<T>()
    }
}

impl<const N: usize> MemorySize for FixedBytes<N> {
    fn self_pointer(&self) -> usize {
        self as *const _ as usize
    }

    fn subtrees(&self) -> Vec<&dyn MemorySize> {
        vec![]
    }

    fn intrinsic_size(&self) -> usize {
        std::mem::size_of::<Self>()
    }
}
/// Implement `MemorySize` for a basic type with no nested allocations.
#[macro_export]
macro_rules! impl_memory_size_for_basic_type {
    ($t:ty) => {
        impl MemorySize for $t {
            // TODO(memsize): Make this optional? This sort of impl doesn't really make sense.
            fn self_pointer(&self) -> usize {
                self as *const _ as usize
            }

            fn subtrees(&self) -> Vec<&dyn MemorySize> {
                vec![]
            }

            fn intrinsic_size(&self) -> usize {
                std::mem::size_of::<Self>()
            }
        }
    };
}
impl_memory_size_for_basic_type!(u8);
impl_memory_size_for_basic_type!(u16);
impl_memory_size_for_basic_type!(u32);
impl_memory_size_for_basic_type!(u64);
impl_memory_size_for_basic_type!(usize);
