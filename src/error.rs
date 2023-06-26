use std::fmt::{Display, Error as FmtError, Formatter};

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
    OutOfBoundsUpdate { index: usize, len: usize },
    OutOfBoundsIterFrom { index: usize, len: usize },
    ListFull { len: usize },
    PackedLeafFull { len: usize },
    LeafUpdateMissing { index: usize },
    PackedLeafOutOfBounds { sub_index: usize, len: usize },
    NodeUpdatesMissing { prefix: usize },
    InvalidListUpdate,
    InvalidVectorUpdate,
    WrongVectorLength { len: usize, expected: usize },
    PushNotSupported,
    UpdateLeafError,
    UpdateLeavesError,
    InvalidDiffDeleteNotSupported,
    InvalidDiffLeaf,
    InvalidDiffNode,
    InvalidDiffPendingUpdates,
    AddToDiffError,
    BuilderExpectedLeaf,
    BuilderStackEmptyMerge,
    BuilderStackEmptyMergeLeft,
    BuilderStackEmptyMergeRight,
    BuilderStackEmptyFinish,
    BuilderStackEmptyFinishLeft,
    BuilderStackEmptyFinishRight,
    BuilderStackEmptyFinalize,
    BuilderStackLeftover,
    BulkUpdateUnclean,
    InvalidZeroLength,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        write!(f, "{:?}", self)
    }
}
