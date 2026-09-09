#!/usr/bin/env python3
"""Compare mem::take and usize::div_ceil with their pinned Rust source bodies."""

import sys

from aeneas_source_model_audit import run_suite

SUITE = {
    "name": "core", "directory": "core_models", "description": __doc__,
    "crate": "core_source", "namespace": "CoreSource",
    "includes": ["core::mem::take", "core::num::_::div_ceil"],
    "source_files": {
        "take": "/rustc/library/core/src/mem/mod.rs",
        "div_ceil": "/rustc/library/core/src/num/uint_macros.rs",
    },
    "proofs": {
        "core_take_agrees": [],
        "core_div_ceil_agrees": ["propext", "Classical.choice", "Quot.sound"],
    },
    "composition": [], "unresolved": [],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
