use crate::{Arc, Leaf, PackedLeaf, Tree};
use std::mem::size_of;
use tokio::sync::RwLock;
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
