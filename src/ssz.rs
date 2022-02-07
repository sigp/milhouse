use crate::List;
use ssz::{read_offset, Decode, DecodeError, BYTES_PER_LENGTH_OFFSET};
use tree_hash::TreeHash;
use typenum::Unsigned;

/// Decodes `bytes` as if it were a list of variable-length items.
///
/// The `ssz::SszDecoder` can also perform this functionality, however it it significantly faster
/// as it is optimized to read same-typed items whilst `ssz::SszDecoder` supports reading items of
/// differing types.
pub fn decode_list_of_variable_length_items<T: Decode + TreeHash + Clone, N: Unsigned>(
    bytes: &[u8],
) -> Result<List<T, N>, DecodeError> {
    let empty_list = || {
        List::empty()
            .map_err(|e| DecodeError::BytesInvalid(format!("Invalid type and length: {:?}", e)))
    };

    if bytes.is_empty() {
        return empty_list();
    }

    let first_offset = read_offset(bytes)?;
    // FIXME: import sanitize or move this func to SSZ
    // sanitize_offset(first_offset, None, bytes.len(), Some(first_offset))?;

    if first_offset % BYTES_PER_LENGTH_OFFSET != 0 || first_offset < BYTES_PER_LENGTH_OFFSET {
        return Err(DecodeError::InvalidListFixedBytesLen(first_offset));
    }

    let num_items = first_offset / BYTES_PER_LENGTH_OFFSET;

    if num_items > N::to_usize() {
        return Err(DecodeError::BytesInvalid(format!(
            "Variable length list of {} items exceeds maximum of {}",
            num_items,
            N::to_usize()
        )));
    }

    let mut builder = List::<T, N>::builder()
        .map_err(|e| DecodeError::BytesInvalid(format!("Invalid type and length: {:?}", e)))?;

    let mut offset = first_offset;
    for i in 1..=num_items {
        let slice_option = if i == num_items {
            bytes.get(offset..)
        } else {
            let start = offset;

            let next_offset = read_offset(&bytes[(i * BYTES_PER_LENGTH_OFFSET)..])?;
            // FIXME: sanitize
            // offset = sanitize_offset(next_offset, Some(offset), bytes.len(), Some(first_offset))?;
            offset = next_offset;

            bytes.get(start..offset)
        };

        let slice = slice_option.ok_or(DecodeError::OutOfBoundsByte { i: offset })?;

        builder.push(T::from_ssz_bytes(slice)?).map_err(|e| {
            DecodeError::BytesInvalid(format!(
                "List of max capacity {} full: {:?}",
                N::to_usize(),
                e
            ))
        })?;
    }

    let (tree, depth, length) = builder
        .finish()
        .map_err(|e| DecodeError::BytesInvalid(format!("Error finishing list builder: {:?}", e)))?;

    Ok(List::from_parts(tree, length, depth))
}
