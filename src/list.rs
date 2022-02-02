use crate::builder::Builder;
use crate::interface::{ImmList, Interface, MutList, PushList};
use crate::iter::Iter;
use crate::serde::ListVisitor;
use crate::utils::{int_log, opt_packing_depth};
use crate::{Error, Tree};
use serde::{ser::SerializeSeq, Deserialize, Deserializer, Serialize, Serializer};
use ssz::{Decode, Encode, SszEncoder, BYTES_PER_LENGTH_OFFSET};
use std::marker::PhantomData;
use std::sync::Arc;
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

#[derive(Debug, PartialEq, Clone)]
pub struct List<T: TreeHash + Clone, N: Unsigned> {
    pub(crate) tree: Arc<Tree<T>>,
    pub(crate) length: usize,
    pub(crate) depth: usize,
    pub(crate) _phantom: PhantomData<N>,
}

impl<T: TreeHash + Clone, N: Unsigned> List<T, N> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }

    pub fn empty() -> Result<Self, Error> {
        // If the leaves are packed then they reduce the depth
        // FIXME(sproul): test really small lists that fit within a single packed leaf
        let depth = Self::depth()?;
        let tree = Tree::empty(depth);

        Ok(Self {
            tree,
            length: 0,
            depth,
            _phantom: PhantomData,
        })
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let depth = Self::depth()?;
        let mut builder = Builder::new(depth);

        for item in iter.into_iter() {
            builder.push(item)?;
        }

        let (tree, depth, length) = builder.finish()?;

        Ok(Self {
            tree,
            length,
            depth,
            _phantom: PhantomData,
        })
    }

    /// This method exists for testing purposes.
    #[doc(hidden)]
    pub fn try_from_iter_slow(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut list = Self::empty()?;

        for item in iter.into_iter() {
            list.push(item)?;
        }

        Ok(list)
    }

    pub fn as_mut(&mut self) -> Interface<T, Self> {
        Interface::new(self)
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    pub fn iter(&self) -> Iter<T> {
        Iter::new(&self.tree, self.depth, self.length)
    }

    // Wrap trait methods so we present a Vec-like interface without having to import anything.
    pub fn get(&self, index: usize) -> Option<&T> {
        ImmList::get(self, index)
    }

    pub fn len(&self) -> usize {
        ImmList::len(self)
    }

    pub fn is_empty(&self) -> bool {
        ImmList::is_empty(self)
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        PushList::push(self, value)
    }

    fn depth() -> Result<usize, Error> {
        if let Some(packing_bits) = opt_packing_depth::<T>() {
            int_log(N::to_usize())
                .checked_sub(packing_bits)
                .ok_or(Error::Oops)
        } else {
            Ok(int_log(N::to_usize()))
        }
    }
}

impl<T: TreeHash + Clone, N: Unsigned> ImmList<T> for List<T, N> {
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            self.tree.get(index, self.depth)
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        self.length
    }
}

impl<T, N> MutList<T> for List<T, N>
where
    T: TreeHash + Clone,
    N: Unsigned,
{
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        Ok(())
    }
}

impl<T, N> PushList<T> for List<T, N>
where
    T: TreeHash + Clone,
    N: Unsigned,
{
    fn push(&mut self, value: T) -> Result<(), Error> {
        if self.length == N::to_usize() {
            return Err(Error::Oops);
        }
        let index = self.length;
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        self.length += 1;
        Ok(())
    }
}

impl<T: TreeHash + Clone, N: Unsigned> Default for List<T, N> {
    fn default() -> Self {
        // FIXME: should probably remove this `Default` implementation
        Self::empty().expect("invalid type and length")
    }
}

impl<T: TreeHash + TreeHash + Clone, N: Unsigned> TreeHash for List<T, N> {
    fn tree_hash_type() -> tree_hash::TreeHashType {
        tree_hash::TreeHashType::List
    }

    fn tree_hash_packed_encoding(&self) -> Vec<u8> {
        unreachable!("List should never be packed.")
    }

    fn tree_hash_packing_factor() -> usize {
        unreachable!("List should never be packed.")
    }

    fn tree_hash_root(&self) -> Hash256 {
        let root = self.tree.tree_hash();
        tree_hash::mix_in_length(&root, self.len())
    }
}

impl<'a, T: TreeHash + Clone, N: Unsigned> IntoIterator for &'a List<T, N> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: TreeHash + Clone, N: Unsigned> Serialize for List<T, N>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for e in self {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}

impl<'de, T, N> Deserialize<'de> for List<T, N>
where
    T: Deserialize<'de> + TreeHash + Clone,
    N: Unsigned,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(ListVisitor::default())
    }
}

// FIXME: duplicated from `ssz::encode::impl_for_vec`
impl<T: Encode + TreeHash + Clone, N: Unsigned> Encode for List<T, N> {
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
        if T::is_ssz_fixed_len() {
            buf.reserve(T::ssz_fixed_len() * self.len());

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

impl<T, N> Decode for List<T, N>
where
    T: Decode + TreeHash + Clone,
    N: Unsigned,
{
    fn is_ssz_fixed_len() -> bool {
        false
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        let max_len = N::to_usize();

        let empty_list = || {
            List::empty().map_err(|e| {
                ssz::DecodeError::BytesInvalid(format!("Invalid type and length: {:?}", e))
            })
        };

        if bytes.is_empty() {
            empty_list()
        } else if T::is_ssz_fixed_len() {
            let num_items = bytes
                .len()
                .checked_div(T::ssz_fixed_len())
                .ok_or(ssz::DecodeError::ZeroLengthItem)?;

            if num_items > max_len {
                return Err(ssz::DecodeError::BytesInvalid(format!(
                    "List of {} items exceeds maximum of {}",
                    num_items, max_len
                )));
            }

            bytes
                .chunks(T::ssz_fixed_len())
                .try_fold(empty_list()?, |mut list, chunk| {
                    list.push(T::from_ssz_bytes(chunk)?).map_err(|e| {
                        ssz::DecodeError::BytesInvalid(format!(
                            "List of max capacity {} full: {:?}",
                            max_len, e
                        ))
                    })?;
                    Ok(list)
                })
        } else {
            crate::ssz::decode_list_of_variable_length_items(bytes)
        }
    }
}
