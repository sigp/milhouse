mod common;

use common::memory_tracker_accuracy_test;
use milhouse::List;
use typenum::U1024;

// These tests MUST be one per file because DHAT measures allocations globally across threads.
#[test]
fn memory_tracker_accuracy_list_u64() {
    let list = || List::<u64, U1024>::new(vec![1; 1024]).unwrap();
    memory_tracker_accuracy_test(list);
}
