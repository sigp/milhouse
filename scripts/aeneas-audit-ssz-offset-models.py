#!/usr/bin/env python3
"""Compare SSZ offset decoding with pinned ethereum_ssz source."""

import sys

from aeneas_source_model_audit import run_suite

SOURCE = "/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/ethereum_ssz-0.10.0/src/"
SUITE = {
    "name": "ssz-offset", "directory": "ssz_offset_models", "description": __doc__,
    "crate": "ssz_source", "namespace": "SszSource", "source_crate": "ssz",
    "cargo_dependency": {"name": "ethereum_ssz", "version": "0.10.0",
                         "files": ["src/decode.rs", "src/encode.rs", "src/lib.rs"]},
    "includes": ["ssz::decode::decode_offset", "ssz::decode::DecodeError",
                 "ssz::BYTES_PER_LENGTH_OFFSET", "core::slice::_::clone_from_slice",
                 "core::slice::_::spec_clone_from"],
    "roots": ["offset_bytes"],
    "dependency_roots": ["ssz::decode::decode_offset"],
    "source_files": {"decode_offset": SOURCE + "decode.rs",
                     "BYTES_PER_LENGTH_OFFSET": SOURCE + "lib.rs"},
    "initializers": ["BYTES_PER_LENGTH_OFFSET"],
    # Keep the private external root through Aeneas pruning and prevent a
    # generated discriminant instance from colliding with the main library.
    # The runner restores these metadata fields and compares the entire LLBC.
    "retain_sources": ["decode_offset"],
    "rename_source_types": {"DecodeError": "SourceDecodeError"},
    "type_source_files": {"DecodeError": SOURCE + "decode.rs"},
    "model_modules": ["Tree.Ssz.Models", "Tree.Ssz.DecodeModels"],
    "model_files": ["Tree/Ssz/Models.lean", "Tree/Ssz/DecodeModels.lean", "Tree/Types.lean"],
    "proofs": {name: ["propext", "Classical.choice", "Quot.sound"] for name in
               ["width_agrees", "decode_offset_agrees", "read_offset_composition_agrees"]},
    "composition": ["read_offset"], "unresolved": ["read_offset", "encode_length"],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
