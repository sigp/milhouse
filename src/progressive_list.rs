use crate::{
    prog_tree::{ProgTree, ProgTreeIter},
    utils::Length,
    Arc, Error, Value,
};
use itertools::process_results;
use ssz::{Decode, Encode, SszEncoder, TryFromIter, BYTES_PER_LENGTH_OFFSET};
use tree_hash::{Hash256, PackedEncoding, TreeHash};

pub struct ProgressiveList<T: Value> {
    tree: Arc<ProgTree<T>>,
    length: Length,
}

impl<T: Value> ProgressiveList<T> {
    pub fn empty() -> Self {
        Self {
            tree: Arc::new(ProgTree::empty()),
            length: Length(0),
        }
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut list = Self::empty();
        for value in iter {
            list.push(value)?;
        }
        Ok(list)
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        self.tree = self.tree.push(value, self.len())?.into();
        *self.length.as_mut() += 1;
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.length.as_usize()
    }

    pub fn iter(&self) -> ProgTreeIter<'_, T> {
        self.tree.iter(self.len())
    }
}

impl<'a, T: Value> IntoIterator for &'a ProgressiveList<T> {
    type Item = &'a T;
    type IntoIter = ProgTreeIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Value + Send + Sync> TreeHash for ProgressiveList<T> {
    fn tree_hash_type() -> tree_hash::TreeHashType {
        tree_hash::TreeHashType::List
    }

    fn tree_hash_packed_encoding(&self) -> PackedEncoding {
        unreachable!("ProgressiveList should never be packed.")
    }

    fn tree_hash_packing_factor() -> usize {
        unreachable!("ProgressiveList should never be packed.")
    }

    fn tree_hash_root(&self) -> Hash256 {
        let root = self.tree.tree_hash();
        tree_hash::mix_in_length(&root, self.len())
    }
}

// FIXME: duplicated from `ssz::encode::impl_for_vec`
impl<T: Value> Encode for ProgressiveList<T> {
    fn is_ssz_fixed_len() -> bool {
        false
    }

    fn ssz_bytes_len(&self) -> usize {
        if <T as Encode>::is_ssz_fixed_len() {
            <T as Encode>::ssz_fixed_len() * self.len()
        } else {
            let mut len = self.iter().map(|item| item.ssz_bytes_len()).sum();
            len += BYTES_PER_LENGTH_OFFSET * self.len();
            len
        }
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        if <T as Encode>::is_ssz_fixed_len() {
            buf.reserve(<T as Encode>::ssz_fixed_len() * self.len());

            for item in self {
                item.ssz_append(buf);
            }
        } else {
            let mut encoder = SszEncoder::container(buf, self.len() * BYTES_PER_LENGTH_OFFSET);

            for item in self {
                encoder.append(item);
            }

            encoder.finalize();
        }
    }
}

impl<T> TryFromIter<T> for ProgressiveList<T>
where
    T: Value,
{
    type Error = Error;

    fn try_from_iter<I>(iter: I) -> Result<Self, Self::Error>
    where
        I: IntoIterator<Item = T>,
    {
        ProgressiveList::try_from_iter(iter)
    }
}

impl<T> Decode for ProgressiveList<T>
where
    T: Value,
{
    fn is_ssz_fixed_len() -> bool {
        false
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        if bytes.is_empty() {
            Ok(ProgressiveList::empty())
        } else if <T as Decode>::is_ssz_fixed_len() {
            let num_items = bytes
                .len()
                .checked_div(<T as Decode>::ssz_fixed_len())
                .ok_or(ssz::DecodeError::ZeroLengthItem)?;

            process_results(
                bytes
                    .chunks(<T as Decode>::ssz_fixed_len())
                    .map(T::from_ssz_bytes),
                |iter| {
                    ProgressiveList::try_from_iter(iter).map_err(|e| {
                        ssz::DecodeError::BytesInvalid(format!(
                            "Error building ssz ProgressiveList: {e:?}"
                        ))
                    })
                },
            )?
        } else {
            ssz::decode_list_of_variable_length_items(bytes, None)
        }
    }
}
