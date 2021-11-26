use crate::interface::{ImmList, Interface, MutList, PushList};
use crate::iter::Iter;
use crate::serde::ListVisitor;
use crate::utils::{borrow_mut, int_log};
use crate::{Error, Tree};
use serde::{ser::SerializeSeq, Deserialize, Deserializer, Serialize, Serializer};
use ssz::{Decode, Encode, SszEncoder, BYTES_PER_LENGTH_OFFSET};
use std::marker::PhantomData;
use std::sync::Arc;
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

#[derive(Debug, PartialEq, Clone)]
pub struct List<T, N: Unsigned> {
    tree: Arc<Tree<T>>,
    length: usize,
    depth: usize,
    _phantom: PhantomData<N>,
}

impl<T: Clone, N: Unsigned> List<T, N> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }

    pub fn empty() -> Self {
        Self::try_from_iter(std::iter::empty()).unwrap()
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let leaves = iter.into_iter().map(Tree::leaf).collect::<Vec<_>>();
        if leaves.len() <= N::to_usize() {
            let length = leaves.len();
            let depth = int_log(N::to_usize());
            let tree = Tree::create(leaves, depth);
            Ok(Self {
                tree,
                length,
                depth,
                _phantom: PhantomData,
            })
        } else {
            Err(Error::Oops)
        }
    }

    pub fn as_mut_ref(&mut self) -> &mut Self {
        self
    }

    pub fn as_mut(&mut self) -> Interface<T, &mut Self> {
        Interface::new(self)
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
}

impl<T: Clone, N: Unsigned> ImmList<T> for List<T, N> {
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

impl<'a, T: Clone, N: Unsigned> ImmList<T> for &'a mut List<T, N> {
    fn get<'s>(&'s self, index: usize) -> Option<&'s T> {
        borrow_mut(self).get(index)
    }

    fn len(&self) -> usize {
        borrow_mut(self).len()
    }
}

impl<'a, T, N> MutList<T> for &'a mut List<T, N>
where
    T: Clone,
    N: Unsigned,
{
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        Ok(())
    }
}

impl<'a, T, N> PushList<T> for &'a mut List<T, N>
where
    T: Clone,
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

impl<T: Clone, N: Unsigned> Default for List<T, N> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<T: TreeHash + Clone, N: Unsigned> TreeHash for List<T, N> {
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

impl<'a, T: Clone, N: Unsigned> IntoIterator for &'a List<T, N> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: Clone, N: Unsigned> Serialize for List<T, N>
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
    T: Deserialize<'de> + Clone,
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
impl<T: Encode + Clone, N: Unsigned> Encode for List<T, N> {
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
    T: Decode + Clone,
    N: Unsigned,
{
    fn is_ssz_fixed_len() -> bool {
        false
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        let max_len = N::to_usize();

        if bytes.is_empty() {
            Ok(List::empty())
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
                .try_fold(List::empty(), |mut list, chunk| {
                    list.as_mut_ref()
                        .push(T::from_ssz_bytes(chunk)?)
                        .map_err(|e| {
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
