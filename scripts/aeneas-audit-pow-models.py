#!/usr/bin/env python3
"""Diagnostic only: attempt the deferred usize::pow source comparison.

The user-approved SOURCE_MODEL_ASSUMPTIONS.json trusts this model for now.
This command remains available to reproduce the upstream failures; it is
excluded from required validation and must not be counted as a passing proof.
"""

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
    print("Diagnostic only: usize::pow source correspondence is currently assumed, not proved.", flush=True)
    sys.exit(run_suite(SUITE))
