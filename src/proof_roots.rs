//! Concrete callers that make trait bodies reachable during extraction.
//!
//! This module is compiled only by `scripts/aeneas-extract.sh`. The callers
//! invoke the real public implementations; they do not replace their bodies.

use crate::{ProgressiveList, UpdateMap, Value};

pub fn progressive_list_eq<T: Value, U: UpdateMap<T> + PartialEq>(
    left: &ProgressiveList<T, U>,
    right: &ProgressiveList<T, U>,
) -> bool {
    left == right
}
