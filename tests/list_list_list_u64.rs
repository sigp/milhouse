mod common;

use common::memory_tracker_accuracy_test;
use milhouse::List;
use typenum::U1024;

// This test runs without the libtest harness (see `Cargo.toml`) because DHAT measures allocations
// globally across threads.
fn main() {
    let list = || {
        List::<List<List<u64, U1024>, U1024>, U1024>::new(vec![
            List::new(vec![
                List::new(vec![1; 1024]).unwrap(),
                List::new(vec![2; 512]).unwrap(),
            ])
            .unwrap(),
            List::new(vec![]).unwrap(),
        ])
        .unwrap()
    };
    memory_tracker_accuracy_test(list);
}
