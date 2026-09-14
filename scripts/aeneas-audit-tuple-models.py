#!/usr/bin/env python3
"""Compare tuple comparison models with their pinned standard-library bodies."""

import sys

from aeneas_source_model_audit import run_suite

METHODS = ("eq", "ne", "partial_cmp", "cmp")
SUITE = {
    "name": "tuple", "directory": "tuple_models", "description": __doc__,
    "crate": "tuple_source", "namespace": "TupleSource",
    "includes": ["core::tuple"],
    "source_prefix": "core::tuple",
    "source_files": {name: "/rustc/library/core/src/tuple.rs" for name in METHODS},
    # These newer trait defaults are not called by the four compared methods.
    # The runner verifies that omitting them leaves all four LLBC declarations intact.
    "excludes": ["core::cmp::PartialOrd::__chaining_" + suffix
                 for suffix in ("lt", "le", "gt", "ge")],
    "proofs": {
        "tuple_eq_agrees": [],
        "tuple_ne_agrees": [],
        "tuple_partial_cmp_agrees": ["propext"],
        "tuple_cmp_agrees": ["propext"],
    },
    "composition": [], "unresolved": [],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
