use milhouse::mem::{MemorySize, MemoryTracker};

#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

/// This is a test runner used in integration tests.
///
/// It lives here because we want to avoid repeating this code across tests, and
/// DHAT tests must be isolated in their own process (integration tests with one test per file).
///
/// See: https://docs.rs/dhat/latest/dhat/#heap-usage-testing
pub fn memory_tracker_accuracy_test<T: MemorySize>(value_producer: impl FnOnce() -> T) {
    let profiler = dhat::Profiler::builder().testing().build();

    // Take a snapshot at the start so we can ignore "background allocations" from e.g. the test
    // runner and the process starting up.
    let pre_stats = dhat::HeapStats::get();

    // We box the value so all its fields are allocated on the heap and DHAT can observe it fully.
    // Some types (like List) include fields with primitive types (like usize) which would be
    // invisible to DHAT if they were allocated on the stack.
    let value = Box::new(value_producer());

    // Calculate the size of the list using Milhouse tools, and then drop the tracker so it isn't
    // consuming any heap space (which would interfere with our measurements).
    let mut mem_tracker = MemoryTracker::default();
    let stats = mem_tracker.track_item(&*value);
    assert_eq!(stats.total_size, mem_tracker.total_size());
    drop(mem_tracker);

    // Calculate total size according to DHAT by subtracting the starting allocations from the
    // current amount allocated.
    let post_stats = dhat::HeapStats::get();
    let dhat_total_size = post_stats.curr_bytes - pre_stats.curr_bytes;

    dhat::assert_eq!(dhat_total_size, stats.total_size);
    drop(profiler);
}
