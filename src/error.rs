use std::fmt::{Display, Error as FmtError, Formatter};

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
    OutOfBoundsUpdate { index: usize, len: usize },
    OutOfBoundsIterFrom { index: usize, len: usize },
    ListFull { len: usize },
    PackedLeafFull { len: usize },
    PushNotSupported,
    Oops,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        write!(f, "{:?}", self)
    }
}
