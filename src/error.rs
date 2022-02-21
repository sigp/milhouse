use std::fmt::{Display, Error as FmtError, Formatter};

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
    OutOfBoundsUpdate { index: usize, len: usize },
    OutOfBoundsIterFrom { index: usize, len: usize },
    ListFull { len: usize },
    PackedLeafFull { len: usize },
    LeafUpdateMissing { index: usize },
    PackedLeafInvalidUpdate { index: usize, prefix: usize },
    NodeUpdatesMissing { prefix: usize },
    InvalidListUpdate,
    InvalidVectorUpdate,
    PushNotSupported,
    UpdateLeafError,
    UpdateLeavesError,
    InvalidDiffZero,
    InvalidDiffLeaf,
    InvalidDiffNode,
    InvalidDiffPendingUpdates,
    AddToDiffError,
    Oops,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        write!(f, "{:?}", self)
    }
}
