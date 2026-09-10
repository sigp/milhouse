#!/usr/bin/env python3
"""Compare usize::pow with its source for either compiler-selector outcome."""

import sys

from aeneas_source_model_audit import run_suite

SUITE = {
    "name": "pow", "directory": "pow_models", "description": __doc__,
    "crate": "pow_source", "namespace": "PowSource",
    "includes": ["core::num::_::pow"],
    "source_files": {"pow": "/rustc/library/core/src/num/uint_macros.rs"},
    "pow_selector": True,
    "proofs": {"core_pow_agrees": ["propext", "Classical.choice", "Quot.sound"]},
    "composition": [], "unresolved": [],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
