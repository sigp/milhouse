use crate::cow::Cow;
use crate::interface::{ImmList, Interface, MutList};
use crate::interface_iter::InterfaceIter;
use crate::iter::Iter;
use crate::utils::{max_btree_index, Length};
use crate::{Arc, Error, List, Tree};
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use ssz::{Decode, Encode, SszEncoder, BYTES_PER_LENGTH_OFFSET};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::marker::PhantomData;
use tree_hash::{Hash256, PackedEncoding, TreeHash};
use typenum::Unsigned;

#[derive(Debug, Derivative, Clone, Serialize, Deserialize)]
#[derivative(PartialEq(bound = "T: TreeHash + Clone + PartialEq, N: Unsigned"))]
#[serde(try_from = "List<T, N>")]
#[serde(into = "List<T, N>")]
#[serde(bound(serialize = "T: TreeHash + Clone + Serialize, N: Unsigned"))]
#[serde(bound(deserialize = "T: TreeHash + Clone + Deserialize<'de>, N: Unsigned"))]
pub struct Vector<T: TreeHash + Clone, N: Unsigned> {
    pub(crate) interface: Interface<T, VectorInner<T, N>>,
}

#[derive(Debug, Derivative, Clone)]
#[derivative(PartialEq(bound = "T: TreeHash + Clone + PartialEq, N: Unsigned"))]
pub struct VectorInner<T: TreeHash + Clone, N: Unsigned> {
    pub(crate) tree: Arc<Tree<T>>,
    pub(crate) depth: usize,
    _phantom: PhantomData<N>,
}

impl<T: TreeHash + Clone, N: Unsigned> Vector<T, N> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        if vec.len() == N::to_usize() {
            Self::try_from(List::new(vec)?)
        } else {
            Err(Error::WrongVectorLength {
                len: vec.len(),
                expected: N::to_usize(),
            })
        }
    }

    pub fn from_elem(elem: T) -> Result<Self, Error> {
        Self::try_from(List::repeat(elem, N::to_usize())?)
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    pub fn iter(&self) -> InterfaceIter<T> {
        self.interface.iter()
    }

    pub fn iter_from(&self, index: usize) -> Result<InterfaceIter<T>, Error> {
        if index > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index,
                len: self.len(),
            });
        }
        Ok(self.interface.iter_from(index))
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
}

impl<T: TreeHash + Clone, N: Unsigned> TryFrom<List<T, N>> for Vector<T, N> {
    type Error = Error;

    fn try_from(list: List<T, N>) -> Result<Self, Error> {
        if list.len() == N::to_usize() {
            let updates = list.interface.updates;
            let backing = VectorInner {
                tree: list.interface.backing.tree,
                depth: list.interface.backing.depth,
                _phantom: PhantomData,
            };
            Ok(Vector {
                interface: Interface { updates, backing },
            })
        } else {
            Err(Error::WrongVectorLength {
                len: list.len(),
                expected: N::to_usize(),
            })
        }
    }
}

impl<T: TreeHash + Clone, N: Unsigned> From<Vector<T, N>> for List<T, N> {
    fn from(vector: Vector<T, N>) -> Self {
        List::from_parts(
            vector.interface.backing.tree,
            vector.interface.backing.depth,
            Length(N::to_usize()),
        )
    }
}

impl<T: TreeHash + Clone, N: Unsigned> ImmList<T> for VectorInner<T, N> {
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.len().as_usize() {
            self.tree.get(index, self.depth)
        } else {
            None
        }
    }

    fn len(&self) -> Length {
        Length(N::to_usize())
    }

    fn iter_from(&self, index: usize) -> Iter<T> {
        Iter::from_index(index, &self.tree, self.depth, Length(N::to_usize()))
    }
}

impl<T, N> MutList<T> for VectorInner<T, N>
where
    T: TreeHash + Clone,
    N: Unsigned,
{
    fn validate_push(_current_len: usize) -> Result<(), Error> {
        Err(Error::PushNotSupported)
    }

    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        if index >= self.len().as_usize() {
            return Err(Error::OutOfBoundsUpdate {
                index,
                len: self.len().as_usize(),
            });
        }
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        Ok(())
    }

    fn update(
        &mut self,
        updates: BTreeMap<usize, T>,
        hash_updates: Option<BTreeMap<(usize, usize), Hash256>>,
    ) -> Result<(), Error> {
        if let Some(max_index) = max_btree_index(&updates) {
            if max_index >= self.len().as_usize() {
                return Err(Error::InvalidVectorUpdate);
            }
        } else {
            // Nothing to do.
            return Ok(());
        }
        self.tree =
            self.tree
                .with_updated_leaves(&updates, 0, self.depth, hash_updates.as_ref())?;
        Ok(())
    }
}

impl<T: Default + TreeHash + Clone, N: Unsigned> Default for Vector<T, N> {
    fn default() -> Self {
        Self::from_elem(T::default()).unwrap_or_else(|e| {
            panic!(
                "Vector::default panicked for length {}: {:?}",
                N::to_usize(),
                e
            )
        })
    }
}

impl<T: TreeHash + Clone + Send + Sync, N: Unsigned> tree_hash::TreeHash for Vector<T, N> {
    fn tree_hash_type() -> tree_hash::TreeHashType {
        tree_hash::TreeHashType::Vector
    }

    fn tree_hash_packed_encoding(&self) -> PackedEncoding {
        unreachable!("Vector should never be packed.")
    }

    fn tree_hash_packing_factor() -> usize {
        unreachable!("Vector should never be packed.")
    }

    fn tree_hash_root(&self) -> Hash256 {
        // FIXME(sproul): remove assert
        assert!(!self.interface.has_pending_updates());
        self.interface.backing.tree.tree_hash()
    }
}

// FIXME: duplicated from `ssz::encode::impl_for_vec`
impl<T: Encode + TreeHash + Clone, N: Unsigned> Encode for Vector<T, N> {
    fn is_ssz_fixed_len() -> bool {
        T::is_ssz_fixed_len()
    }

    fn ssz_fixed_len() -> usize {
        if <Self as ssz::Encode>::is_ssz_fixed_len() {
            T::ssz_fixed_len() * N::to_usize()
        } else {
            BYTES_PER_LENGTH_OFFSET
        }
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

            for item in self.iter() {
                item.ssz_append(buf);
            }
        } else {
            let mut encoder = SszEncoder::container(buf, self.len() * ssz::BYTES_PER_LENGTH_OFFSET);

            for item in self.iter() {
                encoder.append(item);
            }

            encoder.finalize();
        }
    }
}

impl<T: Decode + TreeHash + Clone, N: Unsigned> Decode for Vector<T, N> {
    fn is_ssz_fixed_len() -> bool {
        T::is_ssz_fixed_len()
    }

    fn ssz_fixed_len() -> usize {
        if <Self as ssz::Decode>::is_ssz_fixed_len() {
            T::ssz_fixed_len() * N::to_usize()
        } else {
            ssz::BYTES_PER_LENGTH_OFFSET
        }
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        let list = List::from_ssz_bytes(bytes).map_err(|e| {
            ssz::DecodeError::BytesInvalid(format!("Error decoding vector: {:?}", e))
        })?;
        Self::try_from(list).map_err(|e| {
            ssz::DecodeError::BytesInvalid(format!("Wrong number of vector elements: {:?}", e))
        })
    }
}
