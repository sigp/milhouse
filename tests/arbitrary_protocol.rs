#![cfg(feature = "arbitrary")]

use arbitrary::{Arbitrary, Error, Unstructured};
use milhouse::ProgressiveList;

#[derive(Debug)]
struct Never;

impl<'a> Arbitrary<'a> for Never {
    fn arbitrary(_: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        panic!("a false collection control must not call the element generator")
    }
}

#[test]
fn vector_consumes_even_control_and_stops_at_exhaustion() {
    assert!(
        Vec::<Never>::arbitrary(&mut Unstructured::new(&[]))
            .unwrap()
            .is_empty()
    );
    for control in (0..=254).step_by(2) {
        let bytes = [control, 17, 19];
        let mut input = Unstructured::new(&bytes);
        assert!(Vec::<Never>::arbitrary(&mut input).unwrap().is_empty());
        assert_eq!(input.take_rest(), &[17, 19]);
    }
}

#[derive(Debug)]
struct RejectByte;

impl<'a> Arbitrary<'a> for RejectByte {
    fn arbitrary(input: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        match u8::arbitrary(input)? {
            0 => Ok(Self),
            255 => Err(Error::NotEnoughData),
            _ => panic!("element generation continued after the first error"),
        }
    }
}

#[test]
fn vector_retains_input_at_first_element_error() {
    let mut input = Unstructured::new(&[1, 0, 3, 255, 1, 42]);
    assert!(matches!(
        Vec::<RejectByte>::arbitrary(&mut input),
        Err(Error::NotEnoughData)
    ));
    assert_eq!(input.take_rest(), &[1, 42]);
}

#[derive(Debug)]
struct Replenish;

impl<'a> Arbitrary<'a> for Replenish {
    fn arbitrary(input: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        *input = Unstructured::new(&[0, 42]);
        Ok(Self)
    }
}

#[test]
fn element_generator_can_replace_remaining_input() {
    let mut input = Unstructured::new(&[1]);
    assert_eq!(Vec::<Replenish>::arbitrary(&mut input).unwrap().len(), 1);
    assert_eq!(input.take_rest(), &[42]);
}

#[test]
fn progressive_generator_matches_vector_and_uses_ordinary_take_rest_default() {
    for length in [0, 1, 4, 5, 20, 21, 84, 85, 340, 341] {
        let expected: Vec<u64> = (0..length).collect();
        let mut bytes = Vec::new();
        for value in &expected {
            bytes.push(1);
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        bytes.extend_from_slice(&[2, 1, 99, 0]);
        let mut vector_input = Unstructured::new(&bytes);
        let generated = Vec::<u64>::arbitrary(&mut vector_input).unwrap();
        let mut list_input = Unstructured::new(&bytes);
        let list = ProgressiveList::<u64>::arbitrary(&mut list_input).unwrap();
        assert_eq!(generated, expected);
        assert_eq!(list.len(), expected.len());
        assert_eq!(list.to_vec(), expected);
        assert!(!list.has_pending_updates());
        assert_eq!(list_input.take_rest(), vector_input.take_rest());
        assert_eq!(
            ProgressiveList::<u64>::arbitrary_take_rest(Unstructured::new(&bytes))
                .unwrap()
                .to_vec(),
            expected
        );
    }
    for depth in [0, 1, usize::MAX] {
        assert_eq!(ProgressiveList::<u64>::size_hint(depth), (0, None));
        assert_eq!(
            ProgressiveList::<u64>::try_size_hint(depth).unwrap(),
            (0, None)
        );
    }
}
