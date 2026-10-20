mod common;

use common::memory_tracker_accuracy_test;
use milhouse::List;
use typenum::U1024;

// This test runs without the libtest harness (see `Cargo.toml`) because DHAT measures allocations
// globally across threads.
fn main() {
    let list = || List::<u64, U1024>::new(vec![1; 1024]).unwrap();
    memory_tracker_accuracy_test(list);
}
