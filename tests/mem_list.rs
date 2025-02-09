use milhouse::{mem::MemoryTracker, List};
use typenum::U1024;

#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[test]
fn memory_tracker_accuracy() {
    let _profiler = dhat::Profiler::builder().testing().build();

    // Take a snapshot at the start so we can ignore "background allocations" from e.g. the test
    // runner and the process starting up.
    let pre_stats = dhat::HeapStats::get();

    // We box the list because the MemorySize implementation for List includes the fields of the
    // list, and we want to allocate them on the heap so that they are visible to DHAT.
    let list = Box::new(List::<u64, U1024>::new(vec![1; 1024]).unwrap());

    // Calculate the size of the list using Milhouse tools, and then drop the tracker so it isn't
    // consuming any heap space (which would interfere with our measurements).
    let mut mem_tracker = MemoryTracker::default();
    let stats = mem_tracker.track_item(&*list);
    assert_eq!(stats.total_size, mem_tracker.total_size());
    drop(mem_tracker);

    // Calculate total size according to DHAT by subtracting the starting allocations from the
    // current amount allocated.
    let post_stats = dhat::HeapStats::get();
    let dhat_total_size = post_stats.curr_bytes - pre_stats.curr_bytes;

    dhat::assert_eq!(dhat_total_size, stats.total_size);
}
