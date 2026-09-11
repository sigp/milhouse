# Power model source comparison

**September 7 trial: blocked during extraction.** With the correctly installed
Miri sysroot, Aeneas `7ebd01d19455` rejects `overflow_checks<bool>` in Rust
`nightly-2026-08-18`'s `usize::pow` body (`uint_macros.rs:3635`). Charon
`0.1.251` succeeds, but Aeneas exits 1 and emits partial files. The runner
rejects those files and writes no success report. Native tests passing does
not validate the Lean source comparison.

The same operation remains unsupported with `--monomorphize` and
`--rustc-arg=-Coverflow-checks=yes`. The intrinsic chooses between
`strict_pow` and `wrapping_pow` using the caller's overflow configuration;
its fallback body cannot justify replacing it with a constant. No LLBC
operation or Rust algorithm has been substituted to bypass this failure.
See [the trial status](../../SEPT7_TRIAL_STATUS.md) and
[upstream issue 29](../../UPSTREAM_BUGS.md#29-september-aeneas-cannot-translate-the-overflow-check-selector-in-usizepow).

The successful proof and selector description below record the **June
compiler pin**. They are historical evidence, not a successful comparison
against the September standard library. The current runner command below
reproduces the September failure on the trial branch.

The separate [branch callers](branches.rs) diagnose the candidate's new
algorithm without replacing the original proof root. Full-MIR extraction of
`strict_pow` plus `checked_pow` fails with `Unexpected result: Cps.Unit` at
`Interp.ml:593`. Including `core::num::imp::overflow_panic::pow` does not
resolve it: the panic helper itself translates to `fail panic`, but its
`strict_pow` caller still fails. Thus specializing the outer overflow flag
alone would not suffice. `wrapping_pow` and `overflowing_pow` extract with
external helper templates, but their overflow behavior differs from the
existing checked model; this diagnostic is not a passing comparison proof.

Reproduce the strict branch on the trial branch from the repository root:

```sh
power_probe=$(mktemp -d /tmp/milhouse-power-branch-XXXXXX)
aeneas-lean/.lake/aeneas/charon rustc --preset=aeneas \
  --no-dedup-serialized-ast --start-from power_branch_review::strict \
  --include 'core::num::_::strict_pow' \
  --include 'core::num::_::checked_pow' \
  --include 'core::num::imp::overflow_panic::pow' \
  --dest-file "$power_probe/branch_review.llbc" -- \
  --edition=2024 --crate-type lib --crate-name power_branch_review \
  "$PWD/aeneas-lean/reproducers/pow_models/branches.rs"
aeneas-lean/.lake/aeneas/aeneas -backend lean -namespace BranchReview \
  -split-files -no-progress-bar -print-error-emitters \
  -dest "$power_probe/BranchReview" "$power_probe/branch_review.llbc"
```

The final command is expected to exit 1. Removing the panic-helper include
produces the same failure. The wrapping diagnostic uses root
`power_branch_review::wrapping` and includes only `core::num::_::wrapping_pow`
and `core::num::_::overflowing_pow`. Charon and Aeneas exit zero for that
diagnostic, with external declarations for the compiler selector, `ilog2`,
and `unbounded_shl`. No admitted template or partial output is compiled.

From the repository root:

```sh
python3 scripts/aeneas-audit-pow-models.py
python3 -m unittest discover -s scripts -p test_aeneas_pow_selector.py
```

`core_pow_agrees` in [CheckModels.lean](CheckModels.lean) proves that the entire
freshly extracted `usize::pow` body equals the local `core.num.Usize.pow`
model for every machine-word base and `u32` exponent, including exponent
zero and integer-overflow failure. It assumes no arithmetic bound or loop
termination. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Compiler-selector boundary

With Aeneas `b59d5188`, Charon 0.1.223, and Rust `nightly-2026-06-01`, both
standard-library squaring loops extract completely. The intrinsic
`core::intrinsics::is_val_statically_known` remains an external template
(UPSTREAM_BUGS issue 24). The pinned Rust documentation allows either Bool
outcome and explicitly disallows assuming repeated calls agree.

This comparison supplies one arbitrary Bool outcome through a generated
`PowSource.StaticKnown` class. The theorem quantifies over the class, covering
both branches. The power body queries the intrinsic at most once, so this
parameter does not assume repeated-call consistency. The selector's apparent
`false` fallback is not used to select a preferred branch.

The proof first derives the dynamic loop's mathematical result by induction
on the exponent. An accumulator invariant proves intermediate overflow cannot
be hidden by subsequent multiplication by zero. A second induction proves
that the constant loop followed by its final multiplication agrees with the
dynamic loop, including errors. The full-body theorem then covers either
selector outcome and the zero-exponent early return.

## Provenance and validation

The shared runner checks the source path, crate, transparent whole-body LLBC
provenance, pinned tool versions, and exact intrinsic metadata/signature. It
also checks the outer power body's control flow, which contains the only
intrinsic call. Both arithmetic loops remain freshly extracted.

The sole change to generated `Funs.lean` is the section declaration
`variable [PowSource.StaticKnown]`. The original file is retained beside the
generated modules, both hashes are recorded, and removing that declaration
must reproduce the original byte for byte. No generated function body is
replaced. The admitted external template is inspected but never compiled;
the runner generates a concrete selector definition returning the class's
unconstrained Bool field. There is no default class instance or new axiom.

The report at `.lake/pow-model-audit/report.json` records this separately as
one `parameterizedSourceComparisons` entry with an `abstractCompilerSelectors`
boundary. The source function and both loops are validated; extraction of the
compiler intrinsic itself remains unsupported. Existing Aeneas scalar
primitives, including checked multiplication and exponent halving, remain
foundation abstractions. This is not a compiler-correctness proof.

Four native tests cover 70 base/exponent pairs against repeated multiplication,
five zero-exponent bases, final-bit overflow boundaries, and eight cases with
the two largest exponents. They exercise the overflow-checking build. They
do not establish which compiler-selector outcome executed; Lean covers both.
Four Python tests check exact body preservation and reject five malformed
templates, seven invalid provenance records, and seven altered call/scope
forms.

No production Rust, production model, main extraction, or Aeneas source is
changed. This standalone comparison narrows the numeric model boundary and
does not complete the remaining borrowed CoW or other model-fidelity work.
