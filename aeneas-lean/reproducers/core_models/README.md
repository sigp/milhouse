# Core model source comparisons

This check compares the local `Result::map_err`, `hint::must_use`, blanket
`Borrow::borrow`, `mem::take`, `usize::div_ceil`, `u128::saturating_mul`, and
`u128::checked_pow` models with fresh extraction of their actual pinned Rust
standard-library bodies. The Rust file calls those methods and contains
native protocol tests; it does not
copy their implementations or replace a milhouse operation.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-core-models.py
```

The runner builds `Tree.FunsExternal`, checks Rust formatting, runs eleven native
tests, extracts the seven standard-library bodies into `CoreSource`, checks their
source provenance and completeness, and compiles `CheckModels.lean`. Each run
uses a fresh directory under `.lake/core-model-audit/`; `report.json` records
the input hashes, versions, source spans, and exact proof axiom dependencies.
The previous report is removed before each run.

Tool versions and the Charon preset match the [Option source audit](../option_models/README.md):
Charon 0.1.223, Aeneas `b59d5188`, and `nightly-2026-06-01` Rust commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. Both audit commands share
`scripts/aeneas_source_model_audit.py`. Each suite declares its source paths
and per-theorem axiom policy. The Option suite still requires every comparison
to be axiom-free; this suite permits only standard Lean axioms for ceiling
division, saturation, and checked power and requires the other four comparisons
to be axiom-free. Model inputs include `Tree/Ssz/DecodeModels.lean`, which
defines the error adapter and must-use hint reached by included SSZ decoding.

## Verified behavior

| Comparison | Result |
| --- | --- |
| `Result::map_err` | Equal to the actual body from `core/src/result.rs:962` for every result and arbitrary `FnOnce` dictionary. `Ok` skips the callback; `Err` preserves its actual output, failure, or divergence. The proof is axiom-free and assumes no callback law or termination. |
| `hint::must_use` | Equal to the actual body from `core/src/hint.rs:613` for every value, without axioms. This proves runtime value behavior; compile-time unused-result diagnostics are not modeled. |
| blanket `Borrow::borrow` | Equal to the actual blanket implementation for every value, without axioms or a clone/Borrow dictionary assumption. This is value equality within Aeneas's reference abstraction, not a general pointer-identity theorem. |
| `mem::take` | Equal to the actual body from `core/src/mem/mod.rs:849`, for any value and Default dictionary, including default failure/divergence. Success returns the old value and installs the returned default in the modeled place. The proof is axiom-free. |
| `usize::div_ceil` | Equal to the actual body from `core/src/num/uint_macros.rs:3755` for all machine-word inputs, including zero divisors. The proof uses only `propext`, `Classical.choice`, and `Quot.sound`; it assumes no positivity or size bound. |
| `u128::saturating_mul` | Equal to the actual body from `core/src/num/uint_macros.rs:2516` for every pair of inputs, including overflow. The proof uses only the same three standard Lean axioms, with no bound premise. The called checked multiplication remains an existing Aeneas foundation primitive. |
| `u128::checked_pow` | Equal to the actual body and squaring loop from `core/src/num/uint_macros.rs:2346` for every `u128` base and `u32` exponent. The proof covers zero, termination, and overflow without arithmetic or termination premises, using only the same three standard Lean axioms and the existing checked-multiplication foundation. |

The ceiling-division proof follows Rust's quotient, remainder, and conditional
increment. A nonzero remainder implies both a positive dividend and divisor
greater than one, so rounding remains bounded by the dividend. This proves the
increment cannot introduce an extra overflow case in the local model.

The saturation proof follows the actual match on checked multiplication. A
successful checked product is its mathematical product; an absent product
implies overflow and selects `u128::MAX`. Both branches equal the local minimum
of the mathematical product and that maximum. This compares the entire
`saturating_mul` body, without claiming direct extraction of `checked_mul`.

The checked-power proof follows both parity branches of the extracted loop.
The exponent is positive inside the loop and strictly decreases whenever the
loop continues. The accumulator stays positive unless the base is zero, so
overflow of a reached multiplication implies overflow of the final power.
The loop's mathematical value is `accumulator * base ^ exponent`; parity and
squaring preserve it. The initial accumulator of one establishes the invariant,
and exponent zero returns one directly. These internal invariants add no
assumption to the public comparison.

The native tests check that successful `take` calls Default once, moves the
old value without dropping it, and places the default value in its slot. A
panicking Default leaves the tested original value intact and undropped.
Ceiling division is checked at 24 combinations including `usize::MAX`, plus
three zero-divisor cases. These native checks supplement the universal Lean
equalities; they are not universal panic-state or destructor proofs.
Saturation is checked at 35 pairs covering zero, one, exact products, and
overflow, using a division-based overflow check as the native reference.
Checked power is compared with repeated multiplication at 77 pairs, including
the power-of-two and power-of-three overflow boundaries and `0^0`. That
reference guards multiplication using division. Eight additional checks cover
zero, one, two, and `u128::MAX` at the two largest `u32` exponents.

Four further tests check error-mapping branch/call behavior with moved boxed
values, propagation of a callback panic after one call, must-use movement
without cloning or premature dropping, and the blanket borrow's original
pointer/value with no drop during the call. The Lean error-adapter comparison
also covers divergence; the finite native tests do not test divergence or
establish general destructor/unwind semantics.

The checker rejects missing or opaque source bodies, incorrect source paths,
partial extraction, and unexpected axiom dependencies. Eleven malformed
inventory/report inputs were rejected, including a null structured body and
an injected axiom in the `take` theorem. The Option suite also rejected an
injected `propext` dependency after moving to the shared runner.

All seven compared methods extract completely, with no external templates or
source/metadata replacements. The comparisons still trust
Aeneas's reference/value abstraction and its foundation models, including
`mem::replace` and scalar arithmetic/checked multiplication. Destructor
execution is omitted by extraction; the
native tests observe only their specified concrete cases. No Aeneas source,
production Rust, or local model body changed. These generated modules have a
separate compilation/axiom gate outside the main `Tree` library and do not
increase its theorem count.

## Remaining numeric boundaries

`remaining.rs` preserves independent diagnostic callers for the five numeric
models inspected in this review, including saturation and checked power as controls.
It is separate from the passing audit's proof roots.

| Method | Pinned extraction result / remaining obligation |
| --- | --- |
| `u128::saturating_mul` | Complete body using built-in `U128.checked_mul`; the equality above is proved. |
| `u128::checked_pow` | Complete exponentiation-by-squaring loop using built-in checked multiplication; equality with the local mathematical power model is proved in `3182fd0`. |
| `usize::trailing_zeros` | The body delegates to `core::intrinsics::cttz`, emitted as an external axiom template. |
| `usize::checked_next_power_of_two` | The private `one_less_than_next_power_of_two` helper calls `core::intrinsics::ctlz_nonzero`, emitted as an external axiom template. |
| `usize::pow` | Both squaring loops extract; the selector `core::intrinsics::is_val_statically_known` remains an external template. The separate [power comparison](../pow_models/README.md) now proves the complete body agrees with the local model for either permitted selector outcome (`eb2f91b`). The intrinsic itself remains abstract. |

Reproduce the intrinsic boundaries from the repository root:

```sh
numeric_probe=$(mktemp -d)
../aeneas/charon/bin/charon rustc --preset=aeneas \
  --include 'core::num::_::trailing_zeros' \
  --include 'core::num::_::pow' \
  --include 'core::num::_::checked_next_power_of_two' \
  --include 'core::num::_::one_less_than_next_power_of_two' \
  --include 'core::num::_::checked_pow' \
  --include 'core::num::_::saturating_mul' \
  --dest-file "$numeric_probe/numeric_source.llbc" -- \
  --edition=2024 --crate-type lib --crate-name numeric_source \
  "$PWD/aeneas-lean/reproducers/core_models/remaining.rs"
../aeneas/bin/aeneas -backend lean -namespace NumericSource \
  -split-files -no-progress-bar -dest "$numeric_probe/NumericSource" \
  "$numeric_probe/numeric_source.llbc"
```

Both tools exit zero, but `FunsExternal_Template.lean` contains three missing
intrinsic declarations. Such output is rejected by the passing audit and is
never imported into its comparisons or the main proof library. A separate
fresh run adding `--include core::intrinsics::is_val_statically_known` leaves
the same three templates. The Rust intrinsic's apparent `false` fallback body
does not justify fixing its result to false.

The separate power audit handles only the selector template, validates its
exact provenance and single-call control flow, and quantifies over an arbitrary
Bool outcome. It adds a section parameter to generated Lean without changing
any extracted body. Its report distinguishes this parameterized comparison
from the four direct comparisons in the core suite; it never compiles the
admitted template.

Replacing the six narrow includes with `--include core::num` also attempts
to translate existing foundation primitives. Charon succeeds, but Aeneas
exits 1 on `AddChecked` in `usize::checked_add` and `MulChecked` in
`u128::overflowing_mul` (`InterpExpressions.ml:1153`). This does not invalidate
the comparisons using those existing primitives; it identifies their retained
foundation boundary. To extract only the complete power and saturation bodies,
keep only their two narrow includes and add
`--start-from numeric_source::checked_pow` and
`--start-from numeric_source::saturating_mul`.
That fresh run emits only `Types.lean` and `Funs.lean`, without external
templates or admissions; both generated modules compile. See
[UPSTREAM_BUGS issue 24](../../UPSTREAM_BUGS.md#24-aeneas-numeric-intrinsics-and-overflow-pair-operations).
