use crate::{
    Arc, Cow, Error, UpdateMap, Value,
    progressive_tree::{ProgressiveTree, ProgressiveTreeIter},
    update_map::MaxMap,
    utils::{Length, updated_length},
};
use educe::Educe;
use itertools::process_results;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error as _, ser::SerializeSeq};
use ssz::{BYTES_PER_LENGTH_OFFSET, Decode, Encode, SszEncoder, TryFromIter};
use std::convert::TryFrom;
use tree_hash::{Hash256, PackedEncoding, TreeHash};
use vec_map::VecMap;

#[derive(Debug, Clone, Educe)]
#[educe(PartialEq(bound(T: Value, U: UpdateMap<T> + PartialEq)))]
pub struct ProgressiveList<T: Value, U: UpdateMap<T> = MaxMap<VecMap<T>>> {
    pub(crate) tree: Arc<ProgressiveTree<T>>,
    pub(crate) length: Length,
    pub(crate) updates: U,
}

impl<T: Value, U: UpdateMap<T>> ProgressiveList<T, U> {
    pub fn empty() -> Self {
        Self {
            tree: Arc::new(ProgressiveTree::empty()),
            length: Length(0),
            updates: U::default(),
        }
    }

    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }

    pub fn try_from_iter(iter: impl IntoIterator<Item = T>) -> Result<Self, Error> {
        // Build the backing tree directly from the iterator and take the length from the build,
        // avoiding an intermediate `Vec`.
        let (tree, length) = ProgressiveTree::build_from_iter_with_len(iter)?;
        Ok(Self {
            tree: Arc::new(tree),
            length: Length(length),
            updates: U::default(),
        })
    }

    /// The length of the backing tree, ignoring any pending updates.
    fn backing_len(&self) -> usize {
        self.length.as_usize()
    }

    /// Get the value at `index` from the backing tree only (ignoring pending updates).
    fn backing_get(&self, index: usize) -> Option<&T> {
        if index < self.backing_len() {
            self.tree.get_recursive(index, 0)
        } else {
            None
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.updates.get(index).or_else(|| self.backing_get(index))
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.updates.get_mut_with(index, |index| {
            if index < self.length.as_usize() {
                self.tree.get_recursive(index, 0).cloned()
            } else {
                None
            }
        })
    }

    pub fn get_cow(&mut self, index: usize) -> Option<Cow<'_, T>> {
        self.updates.get_cow_with(index, |index| {
            if index < self.length.as_usize() {
                self.tree.get_recursive(index, 0)
            } else {
                None
            }
        })
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        let index = self.len();
        self.updates.insert(index, value);
        Ok(())
    }

    pub fn len(&self) -> usize {
        updated_length(self.length, &self.updates).as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn has_pending_updates(&self) -> bool {
        !self.updates.is_empty()
    }

    /// Apply all pending updates to the backing tree.
    ///
    /// Updates are applied in ascending index order, which means appends (indices `>= length`)
    /// land at the end of the list one at a time, while replaces (indices `< length`) update
    /// existing leaves in place. The list never has gaps, so this ordering is well-defined.
    pub fn apply_updates(&mut self) -> Result<(), Error> {
        if self.updates.is_empty() {
            return Ok(());
        }

        let updates = std::mem::take(&mut self.updates);
        let new_length = updated_length(self.length, &updates);

        // Apply every pending update in a single walk of the spine, rather than re-walking it once
        // per update.
        self.tree = Arc::new(
            self.tree
                .with_updated_leaves(&updates, self.length.as_usize())?,
        );
        self.length = new_length;
        Ok(())
    }

    pub fn bulk_update(&mut self, updates: U) -> Result<(), Error> {
        if !self.updates.is_empty() {
            return Err(Error::BulkUpdateUnclean);
        }
        self.updates = updates;
        Ok(())
    }

    pub fn iter(&self) -> ProgressiveListIter<'_, T, U> {
        self.iter_from_unchecked(0)
    }

    pub fn iter_from(&self, index: usize) -> Result<ProgressiveListIter<'_, T, U>, Error> {
        // Return an empty iterator at `index == len`, just like slicing.
        if index > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index,
                len: self.len(),
            });
        }
        Ok(self.iter_from_unchecked(index))
    }

    fn iter_from_unchecked(&self, index: usize) -> ProgressiveListIter<'_, T, U> {
        let backing_len = self.backing_len();
        // Seek the backing iterator directly to the merged index (capped at the backing length,
        // since any indices beyond it come purely from pending updates).
        let tree_iter = self.tree.iter_from(index.min(backing_len), backing_len);

        ProgressiveListIter {
            tree_iter,
            updates: &self.updates,
            index,
            length: self.len(),
        }
    }

    pub fn iter_cow(&mut self) -> ProgressiveListIterCow<'_, T, U> {
        self.iter_cow_from_unchecked(0)
    }

    pub fn iter_cow_from(
        &mut self,
        index: usize,
    ) -> Result<ProgressiveListIterCow<'_, T, U>, Error> {
        if index > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index,
                len: self.len(),
            });
        }
        Ok(self.iter_cow_from_unchecked(index))
    }

    fn iter_cow_from_unchecked(&mut self, index: usize) -> ProgressiveListIterCow<'_, T, U> {
        let backing_len = self.backing_len();
        let tree_iter = self.tree.iter_from(index.min(backing_len), backing_len);

        ProgressiveListIterCow {
            tree_iter,
            updates: &mut self.updates,
            index,
        }
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    /// Remove `n` elements from the front of `self`.
    ///
    /// Errors if `n > self.len()`.
    pub fn pop_front(&mut self, n: usize) -> Result<(), Error> {
        self.apply_updates()?;

        if n == 0 {
            return Ok(());
        }
        if n > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index: n,
                len: self.len(),
            });
        }

        // Removing from the front re-indexes every element across the progressive subtrees, so
        // there is nothing to share with the old tree; rebuild from the remaining elements. The
        // remaining iterator is streamed straight into the builder to avoid a temporary `Vec`.
        *self = Self::try_from_iter(self.iter_from(n)?.cloned())?;

        Ok(())
    }
}

impl<T: Value, U: UpdateMap<T>> ProgressiveList<T, U> {
    pub fn rebase(&self, base: &Self) -> Result<Self, Error> {
        let mut rebased = self.clone();
        rebased.rebase_on(base)?;
        Ok(rebased)
    }

    /// Rebase `self` onto `base`, sharing memory between equal subtrees. Pending updates on `self`
    /// are applied first; `base` is used as-is.
    pub fn rebase_on(&mut self, base: &Self) -> Result<(), Error> {
        self.apply_updates()?;

        self.tree = ProgressiveTree::rebase_on(
            &self.tree,
            &base.tree,
            self.length.as_usize(),
            base.length.as_usize(),
        )?;

        Ok(())
    }
}

impl<T: Value, U: UpdateMap<T>> TryFrom<Vec<T>> for ProgressiveList<T, U> {
    type Error = Error;

    fn try_from(vec: Vec<T>) -> Result<Self, Error> {
        Self::try_from_iter(vec)
    }
}

impl<T: Value, U: UpdateMap<T>> Default for ProgressiveList<T, U> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<'a, T: Value, U: UpdateMap<T>> IntoIterator for &'a ProgressiveList<T, U> {
    type Item = &'a T;
    type IntoIter = ProgressiveListIter<'a, T, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Value + Send + Sync, U: UpdateMap<T>> TreeHash for ProgressiveList<T, U> {
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
        assert!(
            !self.has_pending_updates(),
            "ProgressiveList has pending updates at tree_hash_root"
        );

        let root = self.tree.tree_hash();
        tree_hash::mix_in_length(&root, self.len())
    }
}

impl<T: Value + Serialize, U: UpdateMap<T>> Serialize for ProgressiveList<T, U> {
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

// This mirrors `ssz::encode::impl_for_vec`, which we can't reuse directly because it is
// specialised to `Vec` and iterates by reference over our merged view instead.
impl<T: Value, U: UpdateMap<T>> Encode for ProgressiveList<T, U> {
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

impl<T, U> TryFromIter<T> for ProgressiveList<T, U>
where
    T: Value,
    U: UpdateMap<T>,
{
    type Error = Error;

    fn try_from_iter<I>(iter: I) -> Result<Self, Self::Error>
    where
        I: IntoIterator<Item = T>,
    {
        ProgressiveList::try_from_iter(iter)
    }
}

impl<T, U> Decode for ProgressiveList<T, U>
where
    T: Value,
    U: UpdateMap<T>,
{
    fn is_ssz_fixed_len() -> bool {
        false
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        if bytes.is_empty() {
            Ok(ProgressiveList::empty())
        } else if <T as Decode>::is_ssz_fixed_len() {
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

impl<'de, T, U> Deserialize<'de> for ProgressiveList<T, U>
where
    T: Deserialize<'de> + Value,
    U: UpdateMap<T>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Deserialize into a `Vec` first for simplicity; a custom visitor that fed the builder
        // directly would avoid the intermediate allocation.
        Self::try_from_iter(Vec::deserialize(deserializer)?)
            .map_err(|e| D::Error::custom(format!("{e:?}")))
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, T, U> arbitrary::Arbitrary<'a> for ProgressiveList<T, U>
where
    T: arbitrary::Arbitrary<'a> + Value,
    U: UpdateMap<T>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        // Build from a `Vec` so the backing tree and length are always consistent.
        let vec = Vec::<T>::arbitrary(u)?;
        Self::new(vec).map_err(|_| arbitrary::Error::IncorrectFormat)
    }
}

/// Iterator over a [`ProgressiveList`] that merges the backing tree with pending updates.
#[derive(Debug)]
pub struct ProgressiveListIter<'a, T: Value, U: UpdateMap<T>> {
    tree_iter: ProgressiveTreeIter<'a, T>,
    updates: &'a U,
    index: usize,
    length: usize,
}

impl<'a, T: Value, U: UpdateMap<T>> Iterator for ProgressiveListIter<'a, T, U> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.index >= self.length {
            return None;
        }

        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        let backing_value = self.tree_iter.next();

        // Prioritise the value from the update map.
        self.updates.get(index).or(backing_value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.length.saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<T: Value, U: UpdateMap<T>> ExactSizeIterator for ProgressiveListIter<'_, T, U> {}

#[derive(Debug)]
pub struct ProgressiveListIterCow<'a, T: Value, U: UpdateMap<T>> {
    tree_iter: ProgressiveTreeIter<'a, T>,
    updates: &'a mut U,
    index: usize,
}

impl<T: Value, U: UpdateMap<T>> ProgressiveListIterCow<'_, T, U> {
    pub fn next_cow(&mut self) -> Option<(usize, Cow<'_, T>)> {
        let index = self.index;
        self.index += 1;

        // Advance the tree iterator so that it moves in step with this iterator.
        let backing_value = self.tree_iter.next();

        // Construct a CoW pointer using the updated entry from the map, or the corresponding
        // vacant entry and the value from the backing iterator.
        let cow = self.updates.get_cow_with(index, |_| backing_value)?;
        Some((index, cow))
    }
}
