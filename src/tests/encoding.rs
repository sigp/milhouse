use crate::{ProgressiveList, Value};
use ssz::Encode;

fn assert_encoding<T: Value>(list: &ProgressiveList<T>, expected: &[T]) {
    let expected_bytes = expected.to_vec().as_ssz_bytes();
    assert_eq!(list.ssz_bytes_len(), expected_bytes.len());
    assert_eq!(list.as_ssz_bytes(), expected_bytes);
    let mut output = vec![0x12, 0x34, 0x56];
    list.ssz_append(&mut output);
    let mut prefixed = vec![0x12, 0x34, 0x56];
    prefixed.extend_from_slice(&expected_bytes);
    assert_eq!(output, prefixed);
    assert!(!<ProgressiveList<T> as Encode>::is_ssz_fixed_len());
    assert_eq!(<ProgressiveList<T> as Encode>::ssz_fixed_len(), 4);
}

#[test]
fn fixed_encoding_matches_vec_with_pending_updates() {
    for n in [0, 1, 4, 5, 20, 21, 84, 85] {
        let mut values: Vec<u64> = (0..n as u64).collect();
        let split = n / 2;
        let mut list = ProgressiveList::<u64>::new(values[..split].to_vec()).unwrap();
        for value in &values[split..] {
            list.push(*value).unwrap();
        }
        if n > 0 {
            *list.get_mut(0).unwrap() = 123;
            values[0] = 123;
        }
        assert_encoding(&list, &values);
        list.apply_updates().unwrap();
        assert_encoding(&list, &values);
    }
}

#[test]
fn variable_encoding_matches_vec_with_pending_updates() {
    for n in [0, 1, 4, 5, 20, 21, 84, 85] {
        let mut values: Vec<ProgressiveList<u8>> = (0..n)
            .map(|i| ProgressiveList::new(vec![i as u8; i % 6]).unwrap())
            .collect();
        let split = n / 2;
        let mut list =
            ProgressiveList::<ProgressiveList<u8>>::new(values[..split].to_vec()).unwrap();
        for value in &values[split..] {
            list.push(value.clone()).unwrap();
        }
        if n > 0 {
            let replacement = ProgressiveList::new(vec![9, 8, 7]).unwrap();
            *list.get_mut(0).unwrap() = replacement.clone();
            values[0] = replacement;
        }
        assert_encoding(&list, &values);
        list.apply_updates().unwrap();
        assert_encoding(&list, &values);
    }
}
