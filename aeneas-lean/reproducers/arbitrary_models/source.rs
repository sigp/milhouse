use arbitrary::{Arbitrary, Unstructured};

pub fn control<'a>(input: &mut Unstructured<'a>) -> arbitrary::Result<bool> {
    bool::arbitrary(input)
}

pub fn vector<'a, T: Arbitrary<'a>>(input: &mut Unstructured<'a>) -> arbitrary::Result<Vec<T>> {
    Vec::arbitrary(input)
}

pub fn take_rest<'a, T: Arbitrary<'a>>(input: Unstructured<'a>) -> arbitrary::Result<T> {
    T::arbitrary_take_rest(input)
}

pub fn size_hint<'a, T: Arbitrary<'a>>(depth: usize) -> (usize, Option<usize>) {
    T::size_hint(depth)
}

pub fn try_size_hint<'a, T: Arbitrary<'a>>(
    depth: usize,
) -> Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
    T::try_size_hint(depth)
}

#[cfg(test)]
mod tests {
    use super::*;
    use arbitrary::Error;
    use std::cell::Cell;

    thread_local! { static CALLS: Cell<usize> = const { Cell::new(0) }; }

    #[test]
    fn all_control_bytes_and_exhaustion() {
        for byte in 0..=u8::MAX {
            let bytes = [byte, 0xa5, 0x5a];
            let mut input = Unstructured::new(&bytes);
            assert_eq!(control(&mut input), Ok(byte % 2 == 1));
            assert_eq!(input.take_rest(), &bytes[1..]);
        }
        let mut input = Unstructured::new(&[]);
        for _ in 0..3 {
            assert_eq!(control(&mut input), Ok(false));
            assert!(input.is_empty());
        }
    }

    #[test]
    fn one_byte_buffer_overwrites_and_consumes() {
        for initial in 0..=u8::MAX {
            for bytes in [&[][..], &[0xa5][..], &[0x5a, 0xff][..]] {
                let mut input = Unstructured::new(bytes);
                let mut buffer = [initial];
                assert_eq!(input.fill_buffer(&mut buffer), Ok(()));
                assert_eq!(buffer[0], bytes.first().copied().unwrap_or(0));
                assert_eq!(input.take_rest(), &bytes[bytes.len().min(1)..]);
            }
        }
    }

    #[derive(Debug, PartialEq)]
    struct Element(u8);

    impl<'a> Arbitrary<'a> for Element {
        fn arbitrary(input: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            CALLS.set(CALLS.get() + 1);
            let byte = input.bytes(1)?[0];
            if byte == 0xff {
                Err(Error::IncorrectFormat)
            } else {
                Ok(Self(byte))
            }
        }
    }

    #[test]
    fn vector_stopping_and_first_error_preserve_input() {
        for (bytes, expected, remaining, calls) in [
            (&[2, 9][..], Ok(vec![]), &[9][..], 0),
            (&[1, 7, 2, 9][..], Ok(vec![Element(7)]), &[9][..], 1),
            (
                &[1, 7, 1, 0xff, 1, 8][..],
                Err(Error::IncorrectFormat),
                &[1, 8][..],
                2,
            ),
        ] {
            CALLS.set(0);
            let mut input = Unstructured::new(bytes);
            assert_eq!(vector::<Element>(&mut input), expected);
            assert_eq!(input.take_rest(), remaining);
            assert_eq!(CALLS.get(), calls);
        }
    }

    #[derive(Debug, PartialEq)]
    struct ReplacesInput(usize);

    impl<'a> Arbitrary<'a> for ReplacesInput {
        fn arbitrary(input: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let call = CALLS.get() + 1;
            CALLS.set(call);
            *input = Unstructured::new(if call == 1 { &[1, 0] } else { &[0, 9] });
            Ok(Self(call))
        }
    }

    #[test]
    fn vector_generators_can_replace_the_input() {
        CALLS.set(0);
        let mut input = Unstructured::new(&[1]);
        assert_eq!(
            vector(&mut input),
            Ok(vec![ReplacesInput(1), ReplacesInput(2)])
        );
        assert_eq!(input.take_rest(), &[9]);
        assert_eq!(CALLS.get(), 2);
    }

    struct Panics;

    impl<'a> Arbitrary<'a> for Panics {
        fn arbitrary(input: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            CALLS.set(CALLS.get() + 1);
            let _ = input.bytes(1)?;
            panic!("element panic sentinel")
        }
    }

    #[test]
    fn vector_panic_stops_before_later_input() {
        CALLS.set(0);
        let mut input = Unstructured::new(&[1, 7, 1, 8]);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = vector::<Panics>(&mut input);
            }))
            .is_err()
        );
        assert_eq!(input.take_rest(), &[1, 8]);
        assert_eq!(CALLS.get(), 1);
    }

    #[test]
    fn owning_default_uses_the_ordinary_generator() {
        for (bytes, expected) in [
            (&[7][..], Ok(Element(7))),
            (&[0xff][..], Err(Error::IncorrectFormat)),
        ] {
            CALLS.set(0);
            assert_eq!(take_rest::<Element>(Unstructured::new(bytes)), expected);
            assert_eq!(CALLS.get(), 1);
        }
        CALLS.set(0);
        assert!(
            std::panic::catch_unwind(|| {
                let _ = take_rest::<Panics>(Unstructured::new(&[7]));
            })
            .is_err()
        );
        assert_eq!(CALLS.get(), 1);
    }

    struct HintOverride;

    impl<'a> Arbitrary<'a> for HintOverride {
        fn arbitrary(_: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            panic!("size hints must not generate values")
        }

        fn size_hint(depth: usize) -> (usize, Option<usize>) {
            CALLS.set(CALLS.get() + 1);
            (depth, Some(depth))
        }
    }

    #[test]
    fn default_hints_and_override_dispatch() {
        for depth in [0, 1, 20, usize::MAX] {
            assert_eq!(size_hint::<Panics>(depth), (0, None));
            assert_eq!(try_size_hint::<Panics>(depth).unwrap(), (0, None));
            CALLS.set(0);
            assert_eq!(
                try_size_hint::<HintOverride>(depth).unwrap(),
                (depth, Some(depth))
            );
            assert_eq!(CALLS.get(), 1);
        }
    }

    struct PanicHint;

    impl<'a> Arbitrary<'a> for PanicHint {
        fn arbitrary(_: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            panic!("hint queries must not generate values")
        }

        fn size_hint(_: usize) -> (usize, Option<usize>) {
            CALLS.set(CALLS.get() + 1);
            panic!("size-hint panic sentinel")
        }
    }

    #[test]
    fn try_hint_default_preserves_callback_panic() {
        CALLS.set(0);
        assert!(
            std::panic::catch_unwind(|| {
                let _ = try_size_hint::<PanicHint>(usize::MAX);
            })
            .is_err()
        );
        assert_eq!(CALLS.get(), 1);
    }
}
