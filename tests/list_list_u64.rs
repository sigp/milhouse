mod common;

use common::memory_tracker_accuracy_test;
use milhouse::List;
use typenum::U1024;

// These tests MUST be one per file because DHAT measures allocations globally across threads.
#[test]
fn memory_tracker_accuracy_list_list_u64() {
    let list = || {
        List::<List<u64, U1024>, U1024>::new(vec![
            List::new(vec![1; 1024]).unwrap(),
            List::new(vec![2; 512]).unwrap(),
        ])
        .unwrap()
    };
    memory_tracker_accuracy_test(list);
}
