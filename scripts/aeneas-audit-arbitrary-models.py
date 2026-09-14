#!/usr/bin/env python3
"""Compare Arbitrary control and size-hint defaults with pinned source."""

import sys

from aeneas_source_model_audit import run_suite

SOURCE = "/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/arbitrary-1.4.1/src/"
SUITE = {
    "name": "arbitrary", "directory": "arbitrary_models", "description": __doc__,
    "crate": "arbitrary_source", "namespace": "ArbitrarySource", "source_crate": "arbitrary",
    "source_prefix": "arbitrary::Arbitrary",
    "source_prefixes": {"arbitrary": "arbitrary::foreign::core::bool"},
    "cargo_dependency": {"name": "arbitrary", "version": "1.4.1",
                         "files": ["src/foreign/core/bool.rs", "src/foreign/core/num.rs",
                                   "src/unstructured.rs", "src/foreign/alloc/vec.rs", "src/lib.rs",
                                   "src/error.rs"]},
    "includes": ["arbitrary::foreign::core::bool", "arbitrary::foreign::core::num",
                 "arbitrary::unstructured::_::fill_buffer", "arbitrary::unstructured::Unstructured",
                 "arbitrary::error::Error", "arbitrary::Arbitrary", "arbitrary::MaxRecursionReached"],
    "roots": ["control", "size_hint", "try_size_hint"],
    "source_files": {"arbitrary": SOURCE + "foreign/core/bool.rs",
                     "size_hint": SOURCE + "lib.rs", "try_size_hint": SOURCE + "lib.rs"},
    # Unused by all three compared methods. The runner checks their complete
    # expanded declarations before and after this exclusion on every run.
    "excludes": ["arbitrary::Arbitrary::arbitrary_take_rest"],
    # Charon allocates fresh statement IDs globally, and its Statement equality
    # ignores them. Check a one-to-one correspondence and record every change.
    "allow_statement_renumbering": True,
    "rename_source_types": {"Error": "SourceError"},
    "type_source_files": {"Error": SOURCE + "error.rs"},
    # Avoid the first field shadowing the dependency namespace in later fields.
    # Both labels are restored before comparing the entire original LLBC.
    "rename_trait_methods": [{"trait": "Arbitrary", "method": "arbitrary",
                              "replacement": "generate_source", "source_file": SOURCE + "lib.rs"}],
    "model_modules": ["Tree.Arbitrary.Models"],
    "model_files": ["Tree/Arbitrary/Models.lean", "Tree/TypesExternal.lean", "Tree/Types.lean"],
    "proofs": {"control_agrees": ["propext", "Classical.choice", "Quot.sound"],
               "size_hint_default_agrees": ["propext", "Classical.choice", "Quot.sound"],
               "try_size_hint_default_agrees": ["propext"]},
    "composition": [], "unresolved": ["Arbitrary::arbitrary_take_rest", "Vec::arbitrary"],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
