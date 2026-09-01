//! Tests for the `AnyList` view types.

use crate::{AnyList, AnyListMut, AnyListRef, List, ProgressiveList};
use typenum::U128;

type BasicList = List<u64, U128>;
type ProgList = ProgressiveList<u64>;

fn views(n: usize) -> (BasicList, ProgList) {
    let vec: Vec<u64> = (0..n as u64).collect();
    (
        BasicList::new(vec.clone()).unwrap(),
        ProgList::new(vec).unwrap(),
    )
}

#[test]
fn ref_views_agree() {
    let (basic, prog) = views(20);
    let views = [
        AnyListRef::<u64, U128>::Basic(&basic),
        AnyListRef::<u64, U128>::Progressive(&prog),
    ];

    for view in views {
        assert_eq!(view.len(), 20);
        assert!(!view.is_empty());
        assert_eq!(view.get(7), Some(&7));
        assert_eq!(view.get(20), None);
        assert_eq!(view.iter().copied().collect::<Vec<_>>(), basic.to_vec());
        assert_eq!(
            view.iter_from(15).unwrap().copied().collect::<Vec<_>>(),
            vec![15, 16, 17, 18, 19]
        );
        assert_eq!(view.to_vec(), basic.to_vec());
        // Copy semantics: using the view twice is fine.
        assert_eq!(view.len(), view.iter().count());
    }
}

#[test]
fn mut_views_agree() {
    let (mut basic, mut prog) = views(10);

    {
        let muts = [
            AnyListMut::<u64, U128>::Basic(&mut basic),
            AnyListMut::<u64, U128>::Progressive(&mut prog),
        ];

        for mut view in muts {
            *view.get_mut(3).unwrap() = 333;
            view.push(10).unwrap();

            {
                let cow = view.get_cow(4).unwrap();
                *cow.into_mut().unwrap() = 444;
            }

            {
                let mut iter = view.iter_cow();
                while let Some((index, cow)) = iter.next_cow() {
                    if index == 5 {
                        *cow.into_mut().unwrap() = 555;
                    }
                }
            }

            assert!(view.has_pending_updates());
            view.apply_updates().unwrap();
            assert!(!view.has_pending_updates());

            assert_eq!(view.len(), 11);
            assert_eq!(view.get(3), Some(&333));
            assert_eq!(view.get(4), Some(&444));
            assert_eq!(view.get(5), Some(&555));
            assert_eq!(view.get(10), Some(&10));

            view.pop_front(2).unwrap();
            assert_eq!(view.len(), 9);
            assert_eq!(view.get(0), Some(&2));
        }
    }

    // Both underlying lists ended up identical.
    assert_eq!(basic.to_vec(), prog.to_vec());
}

#[test]
fn owned_views() {
    let (basic, prog) = views(5);

    let owned_basic: AnyList<u64, U128> = basic.clone().into();
    let owned_prog: AnyList<u64, U128> = prog.into();

    assert_eq!(owned_basic.to_vec(), vec![0, 1, 2, 3, 4]);
    assert_eq!(owned_basic.to_vec(), owned_prog.to_vec());
    assert_eq!(owned_basic.get(2), Some(&2));
    assert_eq!(owned_prog.iter().count(), 5);

    // Same-arm equality works; mixed arms are unequal by design.
    assert_eq!(owned_basic, AnyList::Basic(basic.clone()));
    assert_ne!(owned_basic, owned_prog);

    // Round-trip through as_ref/to_owned_list.
    let reowned = owned_prog.as_ref().to_owned_list();
    assert_eq!(reowned, owned_prog);

    // Mutation through as_mut.
    let mut owned = owned_basic;
    {
        let mut view = owned.as_mut();
        *view.get_mut(0).unwrap() = 100;
        view.apply_updates().unwrap();
    }
    assert_eq!(owned.get(0), Some(&100));
}
