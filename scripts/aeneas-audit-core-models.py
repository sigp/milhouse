#!/usr/bin/env python3
"""Compare core memory and integer models with their pinned Rust source bodies."""

import sys

from aeneas_source_model_audit import run_suite

SUITE = {
    "name": "core", "directory": "core_models", "description": __doc__,
    "crate": "core_source", "namespace": "CoreSource",
    "includes": ["core::mem::take", "core::num::_::div_ceil",
                 "core::num::_::saturating_mul", "core::num::_::checked_pow"],
    "source_files": {
        "take": "/rustc/library/core/src/mem/mod.rs",
        "div_ceil": "/rustc/library/core/src/num/uint_macros.rs",
        "saturating_mul": "/rustc/library/core/src/num/uint_macros.rs",
        "checked_pow": "/rustc/library/core/src/num/uint_macros.rs",
    },
    "proofs": {
        "core_take_agrees": [],
        "core_div_ceil_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "core_saturating_mul_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "core_checked_pow_agrees": ["propext", "Classical.choice", "Quot.sound"],
    },
    "composition": [], "unresolved": [],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
