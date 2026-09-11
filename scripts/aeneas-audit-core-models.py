#!/usr/bin/env python3
"""Compare core control-flow, borrowing, memory, and integer models with Rust source."""

import sys

from aeneas_source_model_audit import run_suite

SUITE = {
    "name": "core", "directory": "core_models", "description": __doc__,
    "crate": "core_source", "namespace": "CoreSource",
    "includes": ["core::mem::take", "core::num::_::div_ceil",
                 "core::num::_::saturating_mul", "core::num::_::checked_pow",
                 "core::result::_::map_err", "core::hint::must_use", "core::borrow::_::borrow"],
    "source_files": {
        "take": "/rustc/library/core/src/mem/mod.rs",
        "div_ceil": "/rustc/library/core/src/num/uint_macros.rs",
        "saturating_mul": "/rustc/library/core/src/num/uint_macros.rs",
        "checked_pow": "/rustc/library/core/src/num/uint_macros.rs",
        "map_err": "/rustc/library/core/src/result.rs",
        "must_use": "/rustc/library/core/src/hint.rs",
        "borrow": "/rustc/library/core/src/borrow.rs",
    },
    "rename_sources": {"map_err": "map_err_source"},
    "model_modules": ["Tree.FunsExternal", "Tree.CompilerModels"],
    "model_files": ["Tree/FunsExternal.lean", "Tree/Ssz/DecodeModels.lean", "Tree/CompilerModels.lean"],
    "core_selector": True,
    "selector_methods": ["checked_pow"],
    "foundation_bindings": [{
        "method": "is_val_statically_known", "source_prefix": "core::intrinsics", "source_crate": "core",
        "source_file": "/rustc/library/core/src/intrinsics/mod.rs",
        "lean_name": "core.intrinsics.is_val_statically_known",
        "signature": "{T : Type} (markerCopyInst : core.marker.Copy T) : T → Result Bool",
        "intrinsic": {"name": "is_val_statically_known", "arg_names": ["_arg"]},
        "module": "Tree.CompilerModels",
    }] + [{
        "method": name, "source_prefix": "core::num", "source_crate": "core",
        "source_file": "/rustc/library/core/src/num/uint_macros.rs",
        "lean_name": "core.num.U128." + name, "signature": signature,
        "module": "Tree.CompilerModels",
    } for name, signature in [
        ("ilog2", ": Std.U128 → Result Std.U32"),
        ("checked_shl", ": Std.U128 → Std.U32 → Result (Option Std.U128)"),
        ("is_power_of_two", ": Std.U128 → Result Bool"),
    ]],
    "proofs": {
        "core_take_agrees": [],
        "core_div_ceil_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "core_saturating_mul_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "core_checked_pow_agrees": ["propext", "Classical.choice", "Quot.sound"],
        "core_map_err_agrees": [],
        "core_must_use_agrees": [],
        "core_borrow_agrees": [],
    },
    "composition": [], "unresolved": [],
}


if __name__ == "__main__":
    sys.exit(run_suite(SUITE))
