use crate::{
    interface::MutList, tree::TreeDiff, update_map::MaxMap, Error, List, UpdateMap, Vector,
};
use serde::{Deserialize, Serialize};
use ssz::{Decode, Encode};
use ssz_derive::{Decode, Encode};
use std::marker::PhantomData;
use tree_hash::TreeHash;
use typenum::Unsigned;
use vec_map::VecMap;

/// Trait for diffs that can be applied to a given `Target` type.
pub trait Diff: Sized {
    /// The type acted upon.
    type Target;
    /// The type of errors produced by diffing `Target`.
    type Error: From<Error>;

    /// Produce a diff between `orig` and `other` where `other` is an updated version of `orig`.
    fn compute_diff(orig: &Self::Target, other: &Self::Target) -> Result<Self, Self::Error>;

    /// Apply a diff to `target`, updating it mutably.
    fn apply_diff(self, target: &mut Self::Target) -> Result<(), Self::Error>;
}

/// The most primitive type of diff which just stores the entire updated value.
#[derive(Debug, PartialEq, Deserialize, Serialize)]
#[serde(transparent)]
pub struct CloneDiff<T: Clone>(pub T);

impl<T: Clone> Diff for CloneDiff<T> {
    type Target = T;
    type Error = Error;

    fn compute_diff(_: &T, other: &T) -> Result<Self, Error> {
        Ok(CloneDiff(other.clone()))
    }

    fn apply_diff(self, target: &mut T) -> Result<(), Error> {
        *target = self.0;
        Ok(())
    }
}

impl<T> Encode for CloneDiff<T>
where
    T: Encode + Clone,
{
    fn is_ssz_fixed_len() -> bool {
        T::is_ssz_fixed_len()
    }

    fn ssz_fixed_len() -> usize {
        T::ssz_fixed_len()
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        self.0.ssz_append(buf)
    }

    fn ssz_bytes_len(&self) -> usize {
        self.0.ssz_bytes_len()
    }
}

impl<T> Decode for CloneDiff<T>
where
    T: Decode + Clone,
{
    fn is_ssz_fixed_len() -> bool {
        T::is_ssz_fixed_len()
    }

    fn ssz_fixed_len() -> usize {
        T::ssz_fixed_len()
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
        T::from_ssz_bytes(bytes).map(CloneDiff)
    }
}

/// Newtype for List diffs.
#[derive(Debug, PartialEq, Decode, Encode, Deserialize, Serialize)]
#[serde(bound(
    deserialize = "T: TreeHash + PartialEq + Clone + Decode + Encode + Deserialize<'de>",
    serialize = "T: TreeHash + PartialEq + Clone + Decode + Encode + Serialize"
))]
pub struct ListDiff<
    T: TreeHash + PartialEq + Clone + Decode + Encode,
    N: Unsigned,
    U: UpdateMap<T> = MaxMap<VecMap<T>>,
> {
    tree_diff: TreeDiff<T>,
    #[serde(skip, default)]
    #[ssz(skip_serializing, skip_deserializing)]
    _phantom: PhantomData<(N, U)>,
}

impl<T, N, U> Diff for ListDiff<T, N, U>
where
    T: TreeHash + PartialEq + Clone + Decode + Encode,
    N: Unsigned,
    U: UpdateMap<T>,
{
    type Target = List<T, N, U>;
    type Error = Error;

    fn compute_diff(orig: &Self::Target, other: &Self::Target) -> Result<Self, Error> {
        if orig.has_pending_updates() || other.has_pending_updates() {
            return Err(Error::InvalidDiffPendingUpdates);
        }
        let mut tree_diff = TreeDiff::default();
        orig.interface.backing.tree.diff(
            &other.interface.backing.tree,
            0,
            orig.interface.backing.depth,
            &mut tree_diff,
        )?;
        Ok(Self {
            tree_diff,
            _phantom: PhantomData,
        })
    }

    fn apply_diff(self, target: &mut Self::Target) -> Result<(), Error> {
        target
            .interface
            .backing
            .update(self.tree_diff.leaves, Some(self.tree_diff.hashes))
    }
}

/// List diff that gracefully handles removals by falling back to a `CloneDiff`.
///
/// If removals definitely don't need to be handled then a `ListDiff` is preferable as it is
/// more space-efficient.
#[derive(Debug, PartialEq, Decode, Encode, Deserialize, Serialize)]
#[serde(bound(
    deserialize = "T: TreeHash + PartialEq + Clone + Decode + Encode + Deserialize<'de>",
    serialize = "T: TreeHash + PartialEq + Clone + Decode + Encode + Serialize"
))]
#[ssz(enum_behaviour = "union")]
pub enum ResetListDiff<T, N>
where
    T: TreeHash + PartialEq + Clone + Decode + Encode,
    N: Unsigned,
{
    Reset(CloneDiff<List<T, N>>),
    Update(ListDiff<T, N>),
}

impl<T, N> Diff for ResetListDiff<T, N>
where
    T: TreeHash + PartialEq + Clone + Decode + Encode,
    N: Unsigned,
{
    type Target = List<T, N>;
    type Error = Error;

    fn compute_diff(orig: &Self::Target, other: &Self::Target) -> Result<Self, Error> {
        // Detect shortening/removals which the current tree diff algorithm can't handle.
        if other.len() < orig.len() {
            Ok(Self::Reset(CloneDiff(other.clone())))
        } else {
            Ok(Self::Update(ListDiff::compute_diff(orig, other)?))
        }
    }

    fn apply_diff(self, target: &mut Self::Target) -> Result<(), Error> {
        match self {
            Self::Reset(diff) => diff.apply_diff(target),
            Self::Update(diff) => diff.apply_diff(target),
        }
    }
}

/// Newtype for Vector diffs.
#[derive(Debug, PartialEq, Decode, Encode, Deserialize, Serialize)]
#[serde(bound(
    deserialize = "T: TreeHash + PartialEq + Clone + Decode + Encode + Deserialize<'de>",
    serialize = "T: TreeHash + PartialEq + Clone + Decode + Encode + Serialize"
))]
pub struct VectorDiff<
    T: TreeHash + PartialEq + Clone + Decode + Encode,
    N: Unsigned,
    U: UpdateMap<T> = MaxMap<VecMap<T>>,
> {
    tree_diff: TreeDiff<T>,
    #[ssz(skip_serializing, skip_deserializing)]
    _phantom: PhantomData<(N, U)>,
}

impl<T, N, U> Diff for VectorDiff<T, N, U>
where
    T: TreeHash + PartialEq + Clone + Decode + Encode,
    N: Unsigned,
    U: UpdateMap<T>,
{
    type Target = Vector<T, N, U>;
    type Error = Error;

    fn compute_diff(orig: &Self::Target, other: &Self::Target) -> Result<Self, Error> {
        if orig.has_pending_updates() || other.has_pending_updates() {
            return Err(Error::InvalidDiffPendingUpdates);
        }
        let mut tree_diff = TreeDiff::default();
        orig.interface.backing.tree.diff(
            &other.interface.backing.tree,
            0,
            orig.interface.backing.depth,
            &mut tree_diff,
        )?;
        Ok(Self {
            tree_diff,
            _phantom: PhantomData,
        })
    }

    fn apply_diff(self, target: &mut Self::Target) -> Result<(), Error> {
        target
            .interface
            .backing
            .update(self.tree_diff.leaves, Some(self.tree_diff.hashes))
    }
}
