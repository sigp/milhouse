# Core model source comparisons

This check compares the local `mem::take`, `usize::div_ceil`, and
`u128::saturating_mul` models with fresh extraction of their actual pinned
Rust standard-library bodies. The Rust file calls those methods and contains
native protocol tests; it does not
copy their implementations or replace a milhouse operation.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-core-models.py
```

The runner builds `Tree.FunsExternal`, checks Rust formatting, runs five native
tests, extracts the three standard-library bodies into `CoreSource`, checks their
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
division and saturation and requires `take` to be axiom-free.

## Verified behavior

| Comparison | Result |
| --- | --- |
| `mem::take` | Equal to the actual body from `core/src/mem/mod.rs:849`, for any value and Default dictionary, including default failure/divergence. Success returns the old value and installs the returned default in the modeled place. The proof is axiom-free. |
| `usize::div_ceil` | Equal to the actual body from `core/src/num/uint_macros.rs:3755` for all machine-word inputs, including zero divisors. The proof uses only `propext`, `Classical.choice`, and `Quot.sound`; it assumes no positivity or size bound. |
| `u128::saturating_mul` | Equal to the actual body from `core/src/num/uint_macros.rs:2516` for every pair of inputs, including overflow. The proof uses only the same three standard Lean axioms, with no bound premise. The called checked multiplication remains an existing Aeneas foundation primitive. |

The ceiling-division proof follows Rust's quotient, remainder, and conditional
increment. A nonzero remainder implies both a positive dividend and divisor
greater than one, so rounding remains bounded by the dividend. This proves the
increment cannot introduce an extra overflow case in the local model.

The saturation proof follows the actual match on checked multiplication. A
successful checked product is its mathematical product; an absent product
implies overflow and selects `u128::MAX`. Both branches equal the local minimum
of the mathematical product and that maximum. This compares the entire
`saturating_mul` body, without claiming direct extraction of `checked_mul`.

The native tests check that successful `take` calls Default once, moves the
old value without dropping it, and places the default value in its slot. A
panicking Default leaves the tested original value intact and undropped.
Ceiling division is checked at 24 combinations including `usize::MAX`, plus
three zero-divisor cases. These native checks supplement the universal Lean
equalities; they are not universal panic-state or destructor proofs.
Saturation is checked at 35 pairs covering zero, one, exact products, and
overflow, using a division-based overflow check as the native reference.

The checker rejects missing or opaque source bodies, incorrect source paths,
partial extraction, and unexpected axiom dependencies. Eleven malformed
inventory/report inputs were rejected, including a null structured body and
an injected axiom in the `take` theorem. The Option suite also rejected an
injected `propext` dependency after moving to the shared runner.

All three compared methods extract completely. The comparisons still trust
Aeneas's reference/value abstraction and its foundation models, including
`mem::replace` and scalar arithmetic/checked multiplication. Destructor
execution is omitted by extraction; the
native tests observe only their specified concrete cases. No Aeneas source,
production Rust, or local model body changed. These generated modules have a
separate compilation/axiom gate outside the main `Tree` library and do not
increase its theorem count.

## Remaining numeric boundaries

`remaining.rs` preserves independent diagnostic callers for the five numeric
models inspected in this review, including saturation as a control.
It is separate from the passing audit's proof roots.

| Method | Pinned extraction result / remaining obligation |
| --- | --- |
| `u128::saturating_mul` | Complete body using built-in `U128.checked_mul`; the equality above is proved. |
| `u128::checked_pow` | Complete exponentiation-by-squaring loop using built-in checked multiplication. Equality with the local mathematical power model remains unproved. |
| `usize::trailing_zeros` | The body delegates to `core::intrinsics::cttz`, emitted as an external axiom template. |
| `usize::checked_next_power_of_two` | The private `one_less_than_next_power_of_two` helper calls `core::intrinsics::ctlz_nonzero`, emitted as an external axiom template. |
| `usize::pow` | Both squaring loops extract, but their selector `core::intrinsics::is_val_statically_known` remains an external axiom template, even when explicitly included. Rust documents either Boolean result as permitted; a comparison must account for both branches. |

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
