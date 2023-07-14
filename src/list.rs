use crate::builder::Builder;
use crate::diff::{Diff, ListDiff};
use crate::interface::{ImmList, Interface, MutList};
use crate::interface_iter::{InterfaceIter, InterfaceIterCow};
use crate::iter::Iter;
use crate::serde::ListVisitor;
use crate::update_map::MaxMap;
use crate::utils::{arb_arc, int_log, opt_packing_depth, updated_length, Length};
use crate::{Arc, Cow, Error, Tree, UpdateMap, Value};
use arbitrary::Arbitrary;
use derivative::Derivative;
use itertools::process_results;
use serde::{ser::SerializeSeq, Deserialize, Deserializer, Serialize, Serializer};
use ssz::{Decode, Encode, SszEncoder, TryFromIter, BYTES_PER_LENGTH_OFFSET};
use std::collections::BTreeMap;
use std::marker::PhantomData;
use tree_hash::{Hash256, PackedEncoding, TreeHash};
use typenum::Unsigned;
use vec_map::VecMap;

#[derive(Debug, Clone, Derivative, Arbitrary)]
#[derivative(PartialEq(bound = "T: Value, N: Unsigned, U: UpdateMap<T> + PartialEq"))]
#[arbitrary(bound = "T: Arbitrary<'arbitrary> + Value")]
#[arbitrary(bound = "N: Unsigned, U: Arbitrary<'arbitrary> + UpdateMap<T> + PartialEq")]
pub struct List<T: Value, N: Unsigned, U: UpdateMap<T> = MaxMap<VecMap<T>>> {
    pub(crate) interface: Interface<T, ListInner<T, N>, U>,
}

#[derive(Debug, Clone, Derivative, Arbitrary)]
#[derivative(PartialEq(bound = "T: Value, N: Unsigned"))]
#[arbitrary(bound = "T: Arbitrary<'arbitrary> + Value, N: Unsigned")]
pub struct ListInner<T: Value, N: Unsigned> {
    #[arbitrary(with = arb_arc)]
    pub(crate) tree: Arc<Tree<T>>,
    pub(crate) length: Length,
    pub(crate) depth: usize,
    pub(crate) packing_depth: usize,
    #[arbitrary(default)]
    _phantom: PhantomData<N>,
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> List<T, N, U> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }

    pub(crate) fn from_parts(tree: Arc<Tree<T>>, depth: usize, length: Length) -> Self {
        let packing_depth = opt_packing_depth::<T>().unwrap_or(0);
        Self {
            interface: Interface::new(ListInner {
                tree,
                length,
                depth,
                packing_depth,
                _phantom: PhantomData,
            }),
        }
    }

    pub fn empty() -> Self {
        // If the leaves are packed then they reduce the depth
        let depth = Self::depth();
        let tree = Tree::empty(depth);
        Self::from_parts(tree, depth, Length(0))
    }

    pub fn repeat(elem: T, n: usize) -> Result<Self, Error> {
        crate::repeat::repeat_list(elem, n)
    }

    pub fn repeat_slow(elem: T, n: usize) -> Result<Self, Error> {
        Self::try_from_iter(std::iter::repeat(elem).take(n))
    }

    pub fn builder() -> Builder<T> {
        Builder::new(Self::depth())
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut builder = Self::builder();

        for item in iter.into_iter() {
            builder.push(item)?;
        }

        let (tree, depth, length) = builder.finish()?;

        Ok(Self::from_parts(tree, depth, length))
    }

    /// This method exists for testing purposes.
    #[doc(hidden)]
    pub fn try_from_iter_slow(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        let mut list = Self::empty();

        for item in iter.into_iter() {
            list.push(item)?;
        }

        list.apply_updates()?;

        Ok(list)
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    pub fn iter(&self) -> InterfaceIter<T, U> {
        self.interface.iter()
    }

    pub fn iter_from(&self, index: usize) -> Result<InterfaceIter<T, U>, Error> {
        // Return an empty iterator at index == length, just like slicing.
        if index > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index,
                len: self.len(),
            });
        }
        Ok(self.interface.iter_from(index))
    }

    pub fn iter_cow(&mut self) -> InterfaceIterCow<T, U> {
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

    pub fn bulk_update(&mut self, updates: U) -> Result<(), Error> {
        self.interface.bulk_update(updates)
    }

    pub(crate) fn depth() -> usize {
        if let Some(packing_bits) = opt_packing_depth::<T>() {
            int_log(N::to_usize()).saturating_sub(packing_bits)
        } else {
            int_log(N::to_usize())
        }
    }
}

impl<T: Value, N: Unsigned> ImmList<T> for ListInner<T, N> {
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.len().as_usize() {
            self.tree
                .get_recursive(index, self.depth, self.packing_depth)
        } else {
            None
        }
    }

    fn len(&self) -> Length {
        self.length
    }

    fn iter_from(&self, index: usize) -> Iter<T> {
        Iter::from_index(index, &self.tree, self.depth, self.length)
    }
}

impl<T, N> MutList<T> for ListInner<T, N>
where
    T: Value,
    N: Unsigned,
{
    fn validate_push(current_len: usize) -> Result<(), Error> {
        if current_len == N::to_usize() {
            Err(Error::ListFull { len: current_len })
        } else {
            Ok(())
        }
    }

    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        if index > self.len().as_usize() {
            return Err(Error::OutOfBoundsUpdate {
                index,
                len: self.len().as_usize(),
            });
        }

        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        if index == self.length.as_usize() {
            *self.length.as_mut() += 1;
        }
        Ok(())
    }

    fn update<U: UpdateMap<T>>(
        &mut self,
        updates: U,
        hash_updates: Option<BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<(), Error> {
        if let Some(max_index) = updates.max_index() {
            if max_index >= N::to_usize() {
                return Err(Error::InvalidListUpdate);
            }
        } else {
            // Nothing to do.
            return Ok(());
        }
        self.length = updated_length(self.length, &updates);
        self.tree =
            self.tree
                .with_updated_leaves(&updates, 0, self.depth, hash_updates.as_ref())?;
        Ok(())
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> List<T, N, U> {
    pub fn rebase(&self, base: &Self) -> Result<Self, Error> {
        // Diff self from base.
        let diff = ListDiff::compute_diff(base, self)?;

        // Apply diff to base, yielding a new list rooted in base.
        let mut new = base.clone();
        diff.apply_diff(&mut new)?;

        Ok(new)
    }

    pub fn rebase_on(&mut self, base: &Self) -> Result<(), Error> {
        let rebased = self.rebase(base)?;
        *self = rebased;
        Ok(())
    }
}

impl<T: Value, N: Unsigned> Default for List<T, N> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<T: Value + Send + Sync, N: Unsigned> TreeHash for List<T, N> {
    fn tree_hash_type() -> tree_hash::TreeHashType {
        tree_hash::TreeHashType::List
    }

    fn tree_hash_packed_encoding(&self) -> PackedEncoding {
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

impl<'a, T: Value, N: Unsigned, U: UpdateMap<T>> IntoIterator for &'a List<T, N, U> {
    type Item = &'a T;
    type IntoIter = InterfaceIter<'a, T, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Value, N: Unsigned, U: UpdateMap<T>> Serialize for List<T, N, U>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for e in self {
            seq.serialize_element(&e)?;
        }
        seq.end()
    }
}

impl<'de, T, N, U> Deserialize<'de> for List<T, N, U>
where
    T: Deserialize<'de> + Value,
    N: Unsigned,
    U: UpdateMap<T>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(ListVisitor::default())
    }
}

// FIXME: duplicated from `ssz::encode::impl_for_vec`
impl<T: Value, N: Unsigned> Encode for List<T, N> {
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

impl<T, N> TryFromIter<T> for List<T, N>
where
    T: Value,
    N: Unsigned,
{
    type Error = Error;

    fn try_from_iter<I>(iter: I) -> Result<Self, Self::Error>
    where
        I: IntoIterator<Item = T>,
    {
        List::try_from_iter(iter)
    }
}

impl<T, N> Decode for List<T, N>
where
    T: Value,
    N: Unsigned,
{
    fn is_ssz_fixed_len() -> bool {
        false
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        let max_len = N::to_usize();

        if bytes.is_empty() {
            Ok(List::empty())
        } else if <T as Decode>::is_ssz_fixed_len() {
            let num_items = bytes
                .len()
                .checked_div(<T as Decode>::ssz_fixed_len())
                .ok_or(ssz::DecodeError::ZeroLengthItem)?;

            if num_items > max_len {
                return Err(ssz::DecodeError::BytesInvalid(format!(
                    "List of {} items exceeds maximum of {}",
                    num_items, max_len
                )));
            }

            process_results(
                bytes
                    .chunks(<T as Decode>::ssz_fixed_len())
                    .map(T::from_ssz_bytes),
                |iter| {
                    List::try_from_iter(iter).map_err(|e| {
                        ssz::DecodeError::BytesInvalid(format!("Error building ssz List: {:?}", e))
                    })
                },
            )?
        } else {
            ssz::decode_list_of_variable_length_items(bytes, Some(max_len))
        }
    }
}
