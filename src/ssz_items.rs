//! Streaming SSZ item boundaries for `ProgressiveList`.
//!
//! The variable branch follows ethereum_ssz's list decoder: read and validate
//! the next offset before decoding the preceding payload. Keeping the cursor
//! concrete avoids a borrowed `process_results` adapter during extraction.

use ssz::{BYTES_PER_LENGTH_OFFSET, DecodeError, read_offset};

pub(crate) enum SszItems<'a> {
    Fixed {
        remaining: &'a [u8],
        width: usize,
    },
    Variable {
        bytes: &'a [u8],
        first_offset: usize,
        num_items: usize,
        index: usize,
        offset: usize,
    },
}

impl<'a> SszItems<'a> {
    /// Called only for nonempty input, as in the original list decoder.
    pub(crate) fn variable(bytes: &'a [u8]) -> Result<Self, DecodeError> {
        let first_offset = read_offset(bytes)?;
        // The initial sanitize_offset call checks bounds before alignment.
        if first_offset > bytes.len() {
            return Err(DecodeError::OffsetOutOfBounds(first_offset));
        }
        if first_offset % BYTES_PER_LENGTH_OFFSET != 0 || first_offset < BYTES_PER_LENGTH_OFFSET {
            return Err(DecodeError::InvalidListFixedBytesLen(first_offset));
        }
        Ok(Self::Variable {
            bytes,
            first_offset,
            num_items: first_offset / BYTES_PER_LENGTH_OFFSET,
            index: 1,
            offset: first_offset,
        })
    }

    pub(crate) fn next(&mut self) -> Option<Result<&'a [u8], DecodeError>> {
        match self {
            Self::Fixed { remaining, width } => {
                if remaining.is_empty() {
                    return None;
                }
                // Like slice::chunks, pass a short final chunk to the element decoder.
                let end = std::cmp::min(*width, remaining.len());
                let (item, rest) = remaining.split_at(end);
                *remaining = rest;
                Some(Ok(item))
            }
            Self::Variable {
                bytes,
                first_offset,
                num_items,
                index,
                offset,
            } => {
                if *index > *num_items {
                    return None;
                }
                let i = *index;
                *index += 1;
                Some(Self::variable_item(
                    bytes,
                    *first_offset,
                    *num_items,
                    i,
                    offset,
                ))
            }
        }
    }

    fn variable_item(
        bytes: &'a [u8],
        first_offset: usize,
        num_items: usize,
        index: usize,
        offset: &mut usize,
    ) -> Result<&'a [u8], DecodeError> {
        let item = if index == num_items {
            bytes.get(*offset..)
        } else {
            let start = *offset;
            let next_offset = read_offset(&bytes[(index * BYTES_PER_LENGTH_OFFSET)..])?;
            // Preserve sanitize_offset's order, including bounds before decreasing offsets.
            if next_offset < first_offset {
                return Err(DecodeError::OffsetIntoFixedPortion(next_offset));
            }
            if next_offset > bytes.len() {
                return Err(DecodeError::OffsetOutOfBounds(next_offset));
            }
            if start > next_offset {
                return Err(DecodeError::OffsetsAreDecreasing(next_offset));
            }
            *offset = next_offset;
            bytes.get(start..*offset)
        };
        item.ok_or(DecodeError::OutOfBoundsByte { i: *offset })
    }
}
