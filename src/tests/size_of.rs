use crate::{Leaf, OwnedRef, PackedLeaf, Tree};
use parking_lot::RwLock;
use std::mem::size_of;
use tree_hash::Hash256;

/// It's important that the Tree nodes have a predictable size.
#[test]
fn size_of_hash256() {
    assert_eq!(size_of::<Tree<Hash256>>(), 96);
    assert_eq!(size_of::<Leaf<Hash256>>(), 48);
    assert_eq!(size_of::<PackedLeaf<Hash256>>(), 64);

    let rw_lock_size = size_of::<RwLock<Hash256>>();
    assert_eq!(rw_lock_size, 40);

    let owned_ref_size = size_of::<OwnedRef<Tree<Hash256>>>();
    assert_eq!(owned_ref_size, 24);

    assert_eq!(
        size_of::<Tree<Hash256>>(),
        2 * owned_ref_size + rw_lock_size + 8
    );
}

/// It's important that the Tree nodes have a predictable size.
#[test]
fn size_of_u8() {
    assert_eq!(size_of::<Tree<u8>>(), 96);
    assert_eq!(size_of::<Leaf<u8>>(), 48);
    assert_eq!(size_of::<PackedLeaf<u8>>(), 64);

    let rw_lock_size = size_of::<RwLock<u8>>();
    assert_eq!(rw_lock_size, 16);

    let owned_ref_size = size_of::<OwnedRef<Tree<u8>>>();
    assert_eq!(owned_ref_size, 24);

    assert_eq!(size_of::<Tree<u8>>(), 2 * 32 + 24 + 8);
}
