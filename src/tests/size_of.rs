use crate::progressive_tree::ProgressiveTree;
use crate::{Arc, Leaf, PackedLeaf, Tree};
use parking_lot::RwLock;
use std::mem::size_of;
use tree_hash::Hash256;

/// It's important that the Tree nodes have a predictable size.
#[test]
fn size_of_hash256() {
    assert_eq!(size_of::<Tree<Hash256>>(), 64);
    assert_eq!(size_of::<Leaf<Hash256>>(), 48);
    assert_eq!(size_of::<PackedLeaf<Hash256>>(), 64);

    let rw_lock_size = size_of::<RwLock<Hash256>>();
    assert_eq!(rw_lock_size, 40);

    let arc_size = size_of::<Arc<Tree<Hash256>>>();
    assert_eq!(arc_size, 8);

    assert_eq!(size_of::<Tree<Hash256>>(), size_of::<PackedLeaf<Hash256>>());
}

/// It's important that the Tree nodes have a predictable size.
#[test]
fn size_of_u8() {
    assert_eq!(size_of::<Tree<u8>>(), 64);
    assert_eq!(size_of::<Leaf<u8>>(), 48);
    assert_eq!(size_of::<PackedLeaf<u8>>(), 64);
    assert_eq!(
        size_of::<PackedLeaf<u8>>(),
        size_of::<RwLock<Hash256>>() + size_of::<Vec<u8>>()
    );

    let rw_lock_size = size_of::<RwLock<u8>>();
    assert_eq!(rw_lock_size, 16);

    let arc_size = size_of::<Arc<Tree<u8>>>();
    assert_eq!(arc_size, 8);

    assert_eq!(size_of::<Tree<u8>>(), size_of::<PackedLeaf<u8>>());
}

/// The progressive tree nodes should also have a predictable size.
///
/// Unlike `Tree`, the size is independent of `T`: a `ProgressiveNode` holds a cached `Hash256` plus
/// two `Arc` pointers (the binary subtree and the progressive spine), none of which depend on `T`.
#[test]
fn size_of_progressive() {
    assert_eq!(
        size_of::<ProgressiveTree<Hash256>>(),
        size_of::<RwLock<Hash256>>() + 2 * size_of::<Arc<Tree<Hash256>>>()
    );
    assert_eq!(size_of::<ProgressiveTree<Hash256>>(), 56);

    // The size does not depend on the element type.
    assert_eq!(
        size_of::<ProgressiveTree<u8>>(),
        size_of::<ProgressiveTree<Hash256>>()
    );
}
