#!/usr/bin/env python3
"""Compare vector observer/comparison models with their pinned Rust bodies."""

import sys

from aeneas_source_model_audit import run_suite

SUITE = {
    "name": "vec", "directory": "vec_models", "description": __doc__,
    "crate": "vec_source", "namespace": "VecSource", "source_crate": "alloc",
    "source_prefix": "alloc::vec",
    "includes": ["alloc::vec::_::is_empty", "alloc::vec::partial_eq", "core::slice::index::_"],
    "source_files": {
        "is_empty": "/rustc/library/alloc/src/vec/mod.rs",
        "eq": "/rustc/library/alloc/src/vec/partial_eq.rs",
        "ne": "/rustc/library/alloc/src/vec/partial_eq.rs",
    },
    # Prevent builtin name matching from replacing the very bodies being audited.
    # The runner verifies that these two names are the only LLBC changes.
    "rename_sources": {"eq": "eq_source", "ne": "ne_source"},
    "proofs": {
        "vec_is_empty_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "vec_eq_agrees": ["propext", "Quot.sound"],
        "vec_ne_agrees": ["propext", "Quot.sound"],
    },
    "composition": [], "unresolved": ["pop", "next_back"],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
