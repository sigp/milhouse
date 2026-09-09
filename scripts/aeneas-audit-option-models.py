#!/usr/bin/env python3
"""Compare eleven Option bodies and the cloned composition with local models."""

import sys

from aeneas_source_model_audit import check_axiom_output as _check_axioms
from aeneas_source_model_audit import check_llbc as _check_llbc
from aeneas_source_model_audit import run_suite

METHODS = (
    "is_some_and", "is_none_or", "map", "map_or", "unwrap_or_default",
    "ok_or", "or", "unzip", "copied", "branch", "from_residual",
)
PROOFS = tuple(f"option_{name}_agrees" for name in METHODS) + (
    "option_cloned_composition_agrees",
)
SUITE = {
    "name": "option", "directory": "option_models", "description": __doc__,
    "crate": "option_source", "namespace": "OptionSource",
    "includes": ["core::option"],
    "source_files": {name: "/rustc/library/core/src/option.rs" for name in METHODS},
    "proofs": {name: [] for name in PROOFS},
    "composition": ["cloned"], "unresolved": ["cloned"],
}


def check_llbc(data):
    return _check_llbc(data, SUITE)


def check_axiom_output(output):
    return _check_axioms(output, SUITE["proofs"])


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
