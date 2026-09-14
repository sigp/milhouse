#!/usr/bin/env python3
"""Compare the five reached FixedBytes models with pinned alloy-primitives bodies."""

import sys

from aeneas_source_model_audit import run_suite

METHODS = ("clone", "eq", "default", "ZERO", "is_zero")
SOURCE = "/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/alloy-primitives-1.0.0/src/bits/fixed.rs"
SUITE = {
    "name": "fixed-bytes", "directory": "fixed_bytes_models", "description": __doc__,
    "crate": "fixed_source", "namespace": "FixedSource",
    "source_crate": "alloy_primitives",
    "cargo_dependency": {"name": "alloy-primitives", "version": "1.0.0", "files": ["src/bits/fixed.rs"]},
    "includes": ["alloy_primitives::bits::fixed"],
    "roots": ["clone", "eq", "default", "zero", "is_zero"],
    "source_files": {name: SOURCE for name in METHODS},
    "initializers": ["ZERO"],
    "proofs": {
        "fixed_clone_agrees": [],
        "fixed_zero_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "fixed_default_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "fixed_eq_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "fixed_is_zero_agrees": ["propext", "Classical.choice", "Quot.sound"],
    },
    "composition": [], "unresolved": [],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
