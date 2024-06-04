#![no_main]

use libfuzzer_sys::fuzz_target;
use milhouse::builder::Builder;

fuzz_target!(|data: &[u8]| {
    // We use the first byte as 'depth'
    if data.len() < 1 {return}
    let depth = data[0];

    let data = &data[1..];
    let length = data.len();
    if length > 256 {return}

    let mut builder = Builder::<u8>::new(depth as usize, 0);
    for i in 0..length {
        builder.push(data[i]);
    }

    let Ok((arc_tree, depth, len)) = builder.finish() else {return};
});
