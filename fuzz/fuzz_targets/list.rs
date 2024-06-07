#![no_main]

use libfuzzer_sys::fuzz_target;
use milhouse::List;
use typenum::{Unsigned, U16, U32};

fuzz_target!(|data: &[u8]| {
    let length = data.len();
    if length > 256 {return}

    // Create list using .push()
    let mut list1 = List::<u8, U16>::empty();
    for i in 0..length {
        list1.push(data[i]);
    }
    
    list1.apply_updates();

    // Create list using iterator
    let list2 = List::<u8, U16>::try_from_iter(data.iter().copied());
});
