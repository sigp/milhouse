use crate::{level_iter::LevelNode, List};
use typenum::U32;

#[test]
fn level_iter_from_basic() {
    let vec = vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
    let mut list = List::<u64, U32>::new(vec.clone()).unwrap();
    assert_eq!(list.len(), 11);

    let from = 1;
    for (i, level) in list.level_iter_from(from).unwrap().enumerate() {
        let LevelNode::PackedLeaf(leaf) = level else {
            panic!("not a packed leaf: {level:?}")
        };
        assert_eq!(*leaf, vec[i + from]);
    }

    list.pop_front(1).unwrap();
    assert_eq!(list.len(), vec.len() - 1);
    list.pop_front(2).unwrap();
    assert_eq!(list.len(), vec.len() - 3);

    assert_eq!(list.to_vec().as_slice(), &vec[3..]);
}
