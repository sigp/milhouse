use crate::interface::{ImmList, Interface, MutList};
use crate::iter::Iter;
use crate::{Arc, Error, List, Tree};
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use ssz::{Decode, Encode, SszEncoder, BYTES_PER_LENGTH_OFFSET};
use std::convert::TryFrom;
use std::marker::PhantomData;
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

#[derive(Debug, Clone, Serialize, Deserialize, Derivative)]
#[derivative(PartialEq, Hash)]
#[serde(try_from = "List<T, N>")]
#[serde(into = "List<T, N>")]
pub struct Vector<T: TreeHash + Clone, N: Unsigned> {
    pub(crate) tree: Arc<Tree<T>>,
    pub(crate) depth: usize,
    _phantom: PhantomData<N>,
}

impl<T: TreeHash + Clone, N: Unsigned> Vector<T, N> {
    pub fn new(vec: Vec<T>) -> Result<Self, Error> {
        if vec.len() == N::to_usize() {
            Self::try_from(List::new(vec)?)
        } else {
            Err(Error::Oops)
        }
    }

    pub fn from_elem(elem: T) -> Self {
        // FIXME(sproul): propagate Result
        Self::try_from(List::try_from_iter(std::iter::repeat(elem).take(N::to_usize())).unwrap())
            .unwrap()
    }

    pub fn as_mut(&mut self) -> Interface<T, Self> {
        Interface::new(self)
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    pub fn iter(&self) -> Iter<T> {
        Iter::new(&self.tree, self.depth, self.len())
    }

    pub fn iter_from(&self, index: usize) -> Result<Iter<T>, Error> {
        if index > self.len() {
            return Err(Error::OutOfBoundsIterFrom {
                index,
                len: self.len(),
            });
        }
        Ok(Iter::from_index(index, &self.tree, self.depth, self.len()))
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
}

impl<T: TreeHash + Clone, N: Unsigned> TryFrom<List<T, N>> for Vector<T, N> {
    type Error = Error;

    fn try_from(list: List<T, N>) -> Result<Self, Error> {
        if list.len() == N::to_usize() {
            Ok(Vector {
                tree: list.tree,
                depth: list.depth,
                _phantom: PhantomData,
            })
        } else {
            Err(Error::Oops)
        }
    }
}

impl<T: TreeHash + Clone, N: Unsigned> From<Vector<T, N>> for List<T, N> {
    fn from(vector: Vector<T, N>) -> Self {
        List {
            tree: vector.tree,
            length: N::to_usize(),
            depth: vector.depth,
            _phantom: PhantomData,
        }
    }
}

impl<T: TreeHash + Clone, N: Unsigned> ImmList<T> for Vector<T, N> {
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            self.tree.get(index, self.depth)
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        N::to_usize()
    }
}

impl<T, N> MutList<T> for Vector<T, N>
where
    T: TreeHash + Clone,
    N: Unsigned,
{
    fn replace(&mut self, index: usize, value: T) -> Result<(), Error> {
        if index >= self.len() {
            return Err(Error::OutOfBoundsUpdate {
                index,
                len: self.len(),
            });
        }
        self.tree = self.tree.with_updated_leaf(index, value, self.depth)?;
        Ok(())
    }
}

impl<T: Default + TreeHash + Clone, N: Unsigned> Default for Vector<T, N> {
    fn default() -> Self {
        Self::from_elem(T::default())
    }
}

impl<T: TreeHash + Clone, N: Unsigned> tree_hash::TreeHash for Vector<T, N> {
    fn tree_hash_type() -> tree_hash::TreeHashType {
        tree_hash::TreeHashType::Vector
    }

    fn tree_hash_packed_encoding(&self) -> Vec<u8> {
        unreachable!("Vector should never be packed.")
    }

    fn tree_hash_packing_factor() -> usize {
        unreachable!("Vector should never be packed.")
    }

    fn tree_hash_root(&self) -> Hash256 {
        self.tree.tree_hash()
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
