#!/usr/bin/env python3
"""Compare Arbitrary collection control with pinned dependency source."""

import sys

from aeneas_source_model_audit import run_suite

SOURCE = "/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/arbitrary-1.4.1/src/"
SUITE = {
    "name": "arbitrary", "directory": "arbitrary_models", "description": __doc__,
    "crate": "arbitrary_source", "namespace": "ArbitrarySource", "source_crate": "arbitrary",
    "source_prefix": "arbitrary::foreign::core::bool",
    "cargo_dependency": {"name": "arbitrary", "version": "1.4.1",
                         "files": ["src/foreign/core/bool.rs", "src/foreign/core/num.rs",
                                   "src/unstructured.rs", "src/foreign/alloc/vec.rs", "src/lib.rs",
                                   "src/error.rs"]},
    "includes": ["arbitrary::foreign::core::bool", "arbitrary::foreign::core::num",
                 "arbitrary::unstructured::_::fill_buffer", "arbitrary::unstructured::Unstructured",
                 "arbitrary::error::Error", "arbitrary::Arbitrary", "arbitrary::MaxRecursionReached"],
    "roots": ["control"],
    "source_files": {"arbitrary": SOURCE + "foreign/core/bool.rs"},
    "rename_source_types": {"Error": "SourceError"},
    "type_source_files": {"Error": SOURCE + "error.rs"},
    "model_modules": ["Tree.Arbitrary.Models"],
    "model_files": ["Tree/Arbitrary/Models.lean", "Tree/TypesExternal.lean", "Tree/Types.lean"],
    "proofs": {"control_agrees": ["propext", "Classical.choice", "Quot.sound"]},
    "composition": [], "unresolved": ["Arbitrary::arbitrary_take_rest", "Vec::arbitrary"],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
