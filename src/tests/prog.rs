use crate::progressive_tree::ProgressiveTree;
use tree_hash::Hash256;

/// Iterate trees of various sizes, crossing packed-leaf and spine-subtree boundaries.
#[test]
fn prog_tree_iterator() {
    for n in [0u64, 1, 4, 5, 20, 21, 64, 65, 100] {
        let tree = ProgressiveTree::<u64>::build_from_iter(1..=n).unwrap();
        let iter = tree.iter(n as usize);
        assert_eq!(iter.len(), n as usize);
        let collected: Vec<u64> = iter.copied().collect();
        let expected: Vec<u64> = (1..=n).collect();
        assert_eq!(collected, expected, "n={n}");
    }
}

/// Same as `prog_tree_iterator` but for an unpacked element type.
#[test]
fn prog_tree_iterator_hash256() {
    let tree =
        ProgressiveTree::<Hash256>::build_from_iter((1..=10).map(Hash256::repeat_byte)).unwrap();
    let collected: Vec<_> = tree.iter(10).collect();
    let expected: Vec<_> = (1..=10).map(Hash256::repeat_byte).collect();
    assert!(collected.into_iter().eq(expected.iter()));
}

/// The capacity functions must neither panic nor wrap for any `prog_depth`: they saturate at
/// `usize::MAX`, staying monotonic so the spine walks' range comparisons remain sound.
#[test]
fn prog_tree_capacity_saturates() {
    for (lo, hi) in [(30, 31), (31, 32), (32, 33), (63, 64), (64, u32::MAX)] {
        assert!(
            ProgressiveTree::<u64>::capacity_at_depth(lo)
                <= ProgressiveTree::<u64>::capacity_at_depth(hi)
        );
        assert!(
            ProgressiveTree::<u64>::total_capacity_at_depth(lo)
                <= ProgressiveTree::<u64>::total_capacity_at_depth(hi)
        );

        // `u8` has the largest packing factor (32) and thus overflows soonest.
        assert!(
            ProgressiveTree::<u8>::total_capacity_at_depth(lo)
                <= ProgressiveTree::<u8>::total_capacity_at_depth(hi)
        );
    }

    assert_eq!(
        ProgressiveTree::<u8>::total_capacity_at_depth(u32::MAX),
        usize::MAX
    );
}
