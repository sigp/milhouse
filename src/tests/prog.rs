use crate::tree::ProgTree;
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
