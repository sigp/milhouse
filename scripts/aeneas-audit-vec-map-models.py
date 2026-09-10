#!/usr/bin/env python3
"""Check concrete VecMap observers and mutable lookup against slot semantics."""

import sys

from aeneas_source_model_audit import run_suite

SOURCE = "/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/vec_map-0.8.2/src/lib.rs"
STANDARD = ["propext", "Classical.choice", "Quot.sound"]
SUITE = {
    "name": "vec-map", "directory": "vec_map_models", "description": __doc__,
    "crate": "vec_map_source", "namespace": "VecMapSource",
    "source_crate": "vec_map",
    "source_crates": {"as_ref": "core", "as_mut": "core"},
    "source_prefixes": {"as_ref": "core::option", "as_mut": "core::option"},
    "cargo_dependency": {"name": "vec_map", "version": "0.8.2", "files": ["src/lib.rs"]},
    "includes": ["vec_map", "core::option::_::as_ref", "core::option::_::as_mut"],
    "roots": ["new", "len", "is_empty", "get", "get_mut"],
    "source_files": {
        **{name: SOURCE for name in ("new", "len", "is_empty", "get", "get_mut")},
        "as_ref": "/rustc/library/core/src/option.rs",
        "as_mut": "/rustc/library/core/src/option.rs",
    },
    "model_modules": ["Tree.FunsExternal"],
    "model_files": [],
    "proofs": {
        "option_as_ref_eq": [],
        "option_as_mut_eq": STANDARD,
        "vec_map_new_eq": STANDARD,
        "vec_map_len_eq": STANDARD,
        "vec_map_is_empty_eq": STANDARD,
        "vec_map_get_eq": STANDARD,
        "vec_map_get_mut_eq": STANDARD,
    },
    "composition": [],
    "unresolved": ["VecMap::insert iterator/extension dependencies; concrete UpdateMap implementations"],
}
SUITE["proofs"] = {"VecMapSource." + name: axioms for name, axioms in SUITE["proofs"].items()}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
