use crate::{Arc, List, Tree, UpdateMap, Value, Vector};
use alloy_primitives::FixedBytes;
use std::collections::{HashMap, HashSet};
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

/// Compute the bytes owned by `derived` that are not shared with `base`.
///
/// Walks both trees in parallel, comparing `Arc` pointers at each level. When pointers
/// match, the entire subtree is shared and costs 0 — the recursion stops immediately.
/// When pointers differ, the derived node is counted and its children are recursed.
///
/// Complexity: O(dirty_nodes), where dirty_nodes are the tree nodes that differ between
/// the two trees. For a single leaf mutation in a tree of depth D, this visits ~D nodes.
/// For a fully-rewritten tree, it visits all nodes (same as `total_tree_bytes`).
///
/// No allocations, no external state (unlike `MemoryTracker` which builds a `HashMap`).
pub fn cow_tree_bytes<T: Value>(base: &Arc<Tree<T>>, derived: &Arc<Tree<T>>) -> usize {
    if Arc::ptr_eq(base, derived) {
        return 0;
    }

    let self_bytes = node_bytes::<T>(derived);

    match (base.as_ref(), derived.as_ref()) {
        (
            Tree::Node {
                left: bl,
                right: br,
                ..
            },
            Tree::Node {
                left: dl,
                right: dr,
                ..
            },
        ) => self_bytes + cow_tree_bytes(bl, dl) + cow_tree_bytes(br, dr),
        // Structure mismatch or derived is a leaf/zero — count the full derived subtree.
        _ => self_bytes + children_bytes::<T>(derived),
    }
}

/// Total bytes of all nodes in a tree. No sharing baseline.
pub fn total_tree_bytes<T: Value>(tree: &Arc<Tree<T>>) -> usize {
    node_bytes::<T>(tree) + children_bytes::<T>(tree)
}

/// Bytes consumed by a single tree node (not including its children).
fn node_bytes<T: Value>(tree: &Arc<Tree<T>>) -> usize {
    // Every node is an Arc<Tree<T>>: the Arc pointer + the Tree enum.
    let overhead = std::mem::size_of::<Arc<Tree<T>>>() + std::mem::size_of::<Tree<T>>();
    let leaf_data = match tree.as_ref() {
        Tree::PackedLeaf(packed) => packed.values.capacity() * std::mem::size_of::<T>(),
        Tree::Leaf(_) => std::mem::size_of::<Arc<T>>() + std::mem::size_of::<T>(),
        Tree::Node { .. } | Tree::Zero(_) => 0,
    };
    overhead + leaf_data
}

/// Sum of `total_tree_bytes` for a node's children.
fn children_bytes<T: Value>(tree: &Arc<Tree<T>>) -> usize {
    match tree.as_ref() {
        Tree::Node { left, right, .. } => total_tree_bytes(left) + total_tree_bytes(right),
        _ => 0,
    }
}

/// Compute the total unique COW bytes across multiple derived trees relative to a shared base.
///
/// Like `cow_tree_bytes` but deduplicates across all derived trees using a `HashSet` of
/// pointers. Nodes shared with `base` are skipped via `Arc::ptr_eq` (no base walk needed).
/// Nodes shared between derived trees are counted once.
///
/// Complexity: O(total_unique_dirty_nodes) — each unique COW'd node is visited exactly once
/// across all derived trees. The `HashSet` only contains dirty nodes (not base nodes), so it
/// stays small.
pub fn total_unique_cow_tree_bytes<T: Value>(
    base: &Arc<Tree<T>>,
    derived: &[&Arc<Tree<T>>],
) -> usize {
    let mut seen = HashSet::new();
    let mut total = 0;
    for d in derived {
        total += cow_tree_bytes_dedup(base, d, &mut seen);
    }
    total
}

fn cow_tree_bytes_dedup<T: Value>(
    base: &Arc<Tree<T>>,
    derived: &Arc<Tree<T>>,
    seen: &mut HashSet<usize>,
) -> usize {
    // Shared with base — entire subtree is free.
    if Arc::ptr_eq(base, derived) {
        return 0;
    }

    // Already counted from another derived tree — skip.
    if !seen.insert(Arc::as_ptr(derived) as usize) {
        return 0;
    }

    let self_bytes = node_bytes::<T>(derived);

    match (base.as_ref(), derived.as_ref()) {
        (
            Tree::Node {
                left: bl,
                right: br,
                ..
            },
            Tree::Node {
                left: dl,
                right: dr,
                ..
            },
        ) => self_bytes + cow_tree_bytes_dedup(bl, dl, seen) + cow_tree_bytes_dedup(br, dr, seen),
        _ => self_bytes + children_bytes_dedup::<T>(derived, seen),
    }
}

fn children_bytes_dedup<T: Value>(tree: &Arc<Tree<T>>, seen: &mut HashSet<usize>) -> usize {
    match tree.as_ref() {
        Tree::Node { left, right, .. } => {
            let mut total = 0;
            if seen.insert(Arc::as_ptr(left) as usize) {
                total += node_bytes::<T>(left) + children_bytes_dedup::<T>(left, seen);
            }
            if seen.insert(Arc::as_ptr(right) as usize) {
                total += node_bytes::<T>(right) + children_bytes_dedup::<T>(right, seen);
            }
            total
        }
        _ => 0,
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
