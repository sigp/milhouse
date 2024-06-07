#![no_main]

use libfuzzer_sys::fuzz_target;
use milhouse::List;
use typenum::U16;

fuzz_target!(|data: &[u8]| {
    let length = data.len();
    if length > 256 {
        return;
    }

    // Create list using .push()
    let mut list1 = List::<u8, U16>::empty();
    for i in 0..length {
        if list1.push(data[i]).is_err() {
            assert!(i >= 16);
        }
    }

    list1.apply_updates().unwrap();

    // Create list using iterator
    let Ok(list2) = List::<u8, U16>::try_from_iter(data.iter().copied()) else {
        return;
    };

    assert_eq!(list1, list2);
});
