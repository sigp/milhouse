use crate::{
    interface::{Interface, MutList},
    list::ListInner,
    tree::TreeDiff,
    vector::VectorInner,
    Error, List, Vector,
};
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

/// Trait for types which can be mutated via a succinct diff(erence).
pub trait Diff {
    /// The type of diffs produced by and applied to `Self`.
    type Diff;

    /// Produce a diff between `self` and `other` where `other` is an updated version of `self`.
    fn compute_diff(&self, other: &Self) -> Result<Self::Diff, Error>;

    /// Apply a diff to `self`, updating it mutably.
    fn apply_diff(&mut self, diff: Self::Diff) -> Result<(), Error>;
}

/// Trait for types which implement `Diff` by using the entire updated value.
pub trait CloneDiff: Clone {}

impl<T> Diff for T
where
    T: CloneDiff,
{
    type Diff = T;

    fn compute_diff(&self, other: &Self) -> Result<T, Error> {
        Ok(other.clone())
    }

    fn apply_diff(&mut self, diff: T) -> Result<(), Error> {
        *self = diff;
        Ok(())
    }
}

impl<T, N> Diff for ListInner<T, N>
where
    T: PartialEq + TreeHash + Clone,
    N: Unsigned,
{
    type Diff = TreeDiff<T>;

    fn compute_diff(&self, other: &Self) -> Result<Self::Diff, Error> {
        let mut diff = TreeDiff::default();
        self.tree.diff(&other.tree, 0, self.depth, &mut diff)?;
        Ok(diff)
    }

    fn apply_diff(&mut self, diff: Self::Diff) -> Result<(), Error> {
        self.update(diff.leaves, Some(diff.hashes))
    }
}

impl<T, N> Diff for VectorInner<T, N>
where
    T: PartialEq + TreeHash + Clone,
    N: Unsigned,
{
    type Diff = TreeDiff<T>;

    fn compute_diff(&self, other: &Self) -> Result<Self::Diff, Error> {
        let mut diff = TreeDiff::default();
        self.tree.diff(&other.tree, 0, self.depth, &mut diff)?;
        Ok(diff)
    }

    fn apply_diff(&mut self, diff: Self::Diff) -> Result<(), Error> {
        self.update(diff.leaves, Some(diff.hashes))
    }
}

impl<T, B> Diff for Interface<T, B>
where
    T: TreeHash + Clone,
    B: MutList<T> + Diff,
{
    type Diff = B::Diff;

    fn compute_diff(&self, other: &Self) -> Result<Self::Diff, Error> {
        if self.has_pending_updates() || other.has_pending_updates() {
            return Err(Error::InvalidDiffPendingUpdates);
        }
        self.backing.compute_diff(&other.backing)
    }

    fn apply_diff(&mut self, diff: Self::Diff) -> Result<(), Error> {
        self.backing.apply_diff(diff)
    }
}

impl<T, N> Diff for List<T, N>
where
    T: TreeHash + PartialEq + Clone,
    N: Unsigned,
{
    type Diff = TreeDiff<T>;

    fn compute_diff(&self, other: &Self) -> Result<Self::Diff, Error> {
        self.interface.compute_diff(&other.interface)
    }

    fn apply_diff(&mut self, diff: Self::Diff) -> Result<(), Error> {
        self.interface.apply_diff(diff)
    }
}

impl<T, N> Diff for Vector<T, N>
where
    T: TreeHash + PartialEq + Clone,
    N: Unsigned,
{
    type Diff = TreeDiff<T>;

    fn compute_diff(&self, other: &Self) -> Result<Self::Diff, Error> {
        self.interface.compute_diff(&other.interface)
    }

    fn apply_diff(&mut self, diff: Self::Diff) -> Result<(), Error> {
        self.interface.apply_diff(diff)
    }
}

// `CloneDiff` implementations.
impl CloneDiff for u8 {}
impl CloneDiff for u16 {}
impl CloneDiff for u32 {}
impl CloneDiff for u64 {}
impl CloneDiff for usize {}

impl CloneDiff for i8 {}
impl CloneDiff for i16 {}
impl CloneDiff for i32 {}
impl CloneDiff for i64 {}
impl CloneDiff for isize {}

impl CloneDiff for Hash256 {}
