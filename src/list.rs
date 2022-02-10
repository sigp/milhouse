use crate::builder::Builder;
use crate::cow::Cow;
use crate::interface::{ImmList, Interface, MutList};
use crate::interface_iter::{InterfaceIter, InterfaceIterCow};
use crate::iter::Iter;
use crate::serde::ListVisitor;
use crate::utils::{int_log, max_btree_index, opt_packing_depth, updated_length};
use crate::{Arc, Error, Tree};
use itertools::process_results;
use serde::{ser::SerializeSeq, Deserialize, Deserializer, Serialize, Serializer};
use ssz::{Decode, Encode, SszEncoder, BYTES_PER_LENGTH_OFFSET};
use std::collections::BTreeMap;
use std::marker::PhantomData;
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

#[derive(Debug, PartialEq, Clone)]
pub struct List<T: TreeHash + Clone, N: Unsigned> {
    pub(crate) interface: Interface<T, ListInner<T, N>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ListInner<T: TreeHash + Clone, N: Unsigned> {
    pub(crate) tree: Arc<Tree<T>>,
    pub(crate) length: usize,
    pub(crate) depth: usize,
    _phantom: PhantomData<N>,
}

impl<T: TreeHash + Clone, N: Unsigned> List<T, N> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }

    pub(crate) fn from_parts(tree: Arc<Tree<T>>, depth: usize, length: usize) -> Self {
        Self {
            interface: Interface::new(ListInner {
                tree,
                length,
                depth,
                _phantom: PhantomData,
            }),
        }
    }

    pub fn empty() -> Result<Self, Error> {
        // If the leaves are packed then they reduce the depth
        // FIXME(sproul): test really small lists that fit within a single packed leaf
        let depth = Self::depth()?;
        let tree = Tree::empty(depth);
        Ok(Self::from_parts(tree, depth, 0))
    }

    pub fn builder() -> Result<Builder<T>, Error> {
        let depth = Self::depth()?;
        Ok(Builder::new(depth))
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut builder = Self::builder()?;

        for item in iter.into_iter() {
            builder.push(item)?;
        }

        let (tree, depth, length) = builder.finish()?;

        Ok(Self::from_parts(tree, depth, length))
    }

    /// This method exists for testing purposes.
    #[doc(hidden)]
    pub fn try_from_iter_slow(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut list = Self::empty()?;

        for item in iter.into_iter() {
            list.push(item)?;
        }

        list.apply_updates()?;

        Ok(list)
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    pub fn iter(&self) -> InterfaceIter<T> {
        self.interface.iter()
    }

    pub fn iter_from(&self, index: usize) -> Result<InterfaceIter<T>, Error> {
        // Return an empty iterator at index == length, just like slicing.
        if index > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index,
                len: self.len(),
            });
        }
        Ok(self.interface.iter_from(index))
    }

    pub fn iter_cow(&mut self) -> InterfaceIterCow<T> {
        self.interface.iter_cow()
    }

    // Wrap trait methods so we present a Vec-like interface without having to import anything.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.interface.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.interface.get_mut(index)
    }

    pub fn get_cow(&mut self, index: usize) -> Option<Cow<T>> {
        self.interface.get_cow(index)
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        self.interface.push(value)
    }

    pub fn len(&self) -> usize {
        self.interface.len()
    }

    pub fn is_empty(&self) -> bool {
        self.interface.is_empty()
    }

    pub fn has_pending_updates(&self) -> bool {
        self.interface.has_pending_updates()
    }

    pub fn apply_updates(&mut self) -> Result<(), Error> {
        self.interface.apply_updates()
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

impl<T: TreeHash + Clone, N: Unsigned> ImmList<T> for ListInner<T, N> {
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

    fn iter_from(&self, index: usize) -> Iter<T> {
        Iter::from_index(index, &self.tree, self.depth, self.length)
    }
}

impl<T, N> MutList<T> for ListInner<T, N>
where
    T: TreeHash + Clone,
    N: Unsigned,
{
    fn validate_push(&self) -> Result<(), Error> {
        if self.length == N::to_usize() {
            Err(Error::ListFull { len: self.length })
        } else {
            Ok(())
        }
    }

    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        if index > self.len() {
            return Err(Error::OutOfBoundsUpdate {
                index,
                len: self.len(),
            });
        }

        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        if index == self.length {
            self.length += 1;
        }
        Ok(())
    }

    fn update(&mut self, updates: BTreeMap<usize, T>) -> Result<(), Error> {
        if max_btree_index(&updates).map_or(true, |index| index >= N::to_usize()) {
            return Err(Error::InvalidListUpdate);
        }
        self.length = updated_length(self.length, &updates);
        self.tree = self.tree.with_updated_leaves(updates, 0, self.depth)?;
        Ok(())
    }
}

impl<T: TreeHash + Clone, N: Unsigned> Default for List<T, N> {
    fn default() -> Self {
        // FIXME: should probably remove this `Default` implementation
        Self::empty().expect("invalid type and length")
    }
}

impl<T: TreeHash + Clone + Send + Sync, N: Unsigned> TreeHash for List<T, N> {
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
        // FIXME(sproul): remove assert
        assert!(!self.interface.has_pending_updates());

        let root = self.interface.backing.tree.tree_hash();
        tree_hash::mix_in_length(&root, self.len())
    }
}

impl<'a, T: TreeHash + Clone, N: Unsigned> IntoIterator for &'a List<T, N> {
    type Item = &'a T;
    type IntoIter = InterfaceIter<'a, T>;

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

        if bytes.is_empty() {
            List::empty().map_err(|e| {
                ssz::DecodeError::BytesInvalid(format!("Invalid type and length: {:?}", e))
            })
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

            process_results(
                bytes.chunks(T::ssz_fixed_len()).map(T::from_ssz_bytes),
                |iter| {
                    List::try_from_iter(iter).map_err(|e| {
                        ssz::DecodeError::BytesInvalid(format!("Error building ssz List: {:?}", e))
                    })
                },
            )?
        } else {
            crate::ssz::decode_list_of_variable_length_items(bytes)
        }
    }
}
