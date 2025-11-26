use crate::prog_tree::ProgTree;
use tree_hash::Hash256;

#[test]
fn wow() {
    let empty = ProgTree::<Hash256>::empty();

    let one = empty.push(Hash256::repeat_byte(0x11), 0).unwrap();

    let two = one.push(Hash256::repeat_byte(0x22), 1).unwrap();

    println!("{two:#?}");

    let three = two.push(Hash256::repeat_byte(0x33), 2).unwrap();

    println!("{three:#?}");
}

#[test]
fn wow_u64() {
    let mut tree = ProgTree::<u64>::empty();

    for i in 1..=65 {
        tree = tree.push(i, i as usize - 1).unwrap();
    }

    println!("{tree:#?}");
}
