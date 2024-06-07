#![no_main]

use libfuzzer_sys::fuzz_target;
use milhouse::builder::Builder;

fuzz_target!(|data: &[u8]| {
    // We use the first byte as 'depth'
    if data.len() < 1 {
        return;
    }
    let depth = data[0];

    let data = &data[1..];
    let length = data.len();
    if length > 256 {
        return;
    }

    let Ok(mut builder) = Builder::<u8>::new(depth as usize, 0) else {
        return;
    };
    for i in 0..length {
        if builder.push(data[i]).is_err() {
            assert!(i > (1 << depth));
        }
    }

    let Ok((arc_tree, tree_depth, len)) = builder.finish() else {
        return;
    };
    assert_eq!(tree_depth, depth as usize);
    assert!(len.as_usize() <= length);
    assert_eq!(arc_tree.compute_len(), len.as_usize());
});
