use crate::{List, ProgressiveList};
use tree_hash::TreeHash;
use typenum::U1024;

#[test]
fn list_items_root_matches_tree_hash_root() {
    for len in [0, 1, 2, 17, 1024] {
        let items: Vec<u64> = (0..len).collect();
        let list = List::<u64, U1024>::new(items).unwrap();

        let items_root = list.tree_hash_items_root();
        let expected = tree_hash::mix_in_length(&items_root, list.len());

        assert_eq!(
            list.tree_hash_root(),
            expected,
            "mix_in_length(items_root, len) must equal tree_hash_root for len={len}"
        );
    }
}

#[test]
fn progressive_list_items_root_matches_tree_hash_root() {
    for len in [0, 1, 2, 5, 17, 100] {
        let items: Vec<u64> = (0..len).collect();
        let list = ProgressiveList::<u64>::try_from(items).unwrap();

        let items_root = list.tree_hash_items_root();
        let expected = tree_hash::mix_in_length(&items_root, list.len());

        assert_eq!(
            list.tree_hash_root(),
            expected,
            "mix_in_length(items_root, len) must equal tree_hash_root for len={len}"
        );
    }
}
