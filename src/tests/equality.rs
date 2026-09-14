use crate::utils::Length;
use crate::{Arc, Leaf, PackedLeaf, ProgressiveList, Tree, progressive_tree::ProgressiveTree};
use parking_lot::RwLock;
use ssz_derive::{Decode, Encode};
use tree_hash::Hash256;
use tree_hash_derive::TreeHash;

#[derive(Clone, Debug, Encode, Decode, TreeHash)]
struct NonReflexive {
    value: u64,
}

impl PartialEq for NonReflexive {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

fn nonreflexive_tree() -> Arc<ProgressiveTree<NonReflexive>> {
    Arc::new(ProgressiveTree::ProgressiveNode {
        hash: RwLock::new(Hash256::ZERO),
        left: Arc::new(Tree::PackedLeaf(PackedLeaf {
            hash: RwLock::new(Hash256::ZERO),
            values: vec![NonReflexive { value: 7 }],
        })),
        right: Arc::new(ProgressiveTree::ProgressiveZero),
    })
}

#[test]
fn shared_subtrees_skip_nonreflexive_packed_comparisons() {
    let tree = nonreflexive_tree();
    let left: ProgressiveList<NonReflexive> = ProgressiveList {
        tree: tree.clone(),
        length: Length(1),
        updates: Default::default(),
    };
    assert_eq!(left, left.clone());

    // Distinct progressive nodes still share their binary subtree. Comparing
    // that subtree must retain Arc's pointer shortcut, even for nonreflexive T.
    let shared_children = ProgressiveList {
        tree: Arc::new((*tree).clone()),
        length: Length(1),
        updates: Default::default(),
    };
    assert_eq!(left, shared_children);

    let distinct = ProgressiveList {
        tree: nonreflexive_tree(),
        length: Length(1),
        updates: Default::default(),
    };
    assert_ne!(left, distinct);
}

#[test]
fn structural_equality_ignores_hash_caches() {
    let make = |cache| -> ProgressiveList<u64> {
        let hash = Hash256::from([cache; 32]);
        ProgressiveList {
            tree: Arc::new(ProgressiveTree::ProgressiveNode {
                hash: RwLock::new(hash),
                left: Arc::new(Tree::Node {
                    hash: RwLock::new(hash),
                    left: Arc::new(Tree::Leaf(Leaf::with_hash(7, hash))),
                    right: Arc::new(Tree::Zero(0)),
                }),
                right: Arc::new(ProgressiveTree::ProgressiveZero),
            }),
            length: Length(1),
            updates: Default::default(),
        }
    };
    assert_eq!(make(0), make(1));
}
