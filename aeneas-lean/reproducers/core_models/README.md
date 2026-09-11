# Core model source comparisons

The September 7 compiler validates seven comparisons with freshly extracted
Rust standard-library bodies: `Result::map_err`, `hint::must_use`, blanket
`Borrow::borrow`, `mem::take`, `usize::div_ceil`, `u128::saturating_mul`, and
`u128::checked_pow`. The Rust fixture calls these methods without copying
their implementations.

Run from the repository root after following the [toolchain setup](../../README.md):

```sh
python3 scripts/aeneas-audit-core-models.py
```

The pins in `aeneas-toolchain.json` select Aeneas `7ebd01d19455`, Charon
`0.1.251` (`85bba1f2a64d`), Rust `nightly-2026-08-18`
(`8fa1c96cfd489e4c27654c144ae871ce2c4db6c6`), and Lean 4.31.0.
Miri and rustfmt must be installed for that nightly. The runner rejects a
fallback to Rust's distributed optimized sysroot.

The complete runner passes all seven proofs and eleven native tests. Four
proofs remain axiom-free: error mapping, must-use, blanket borrowing, and
memory take. Division, saturation, and checked power use only `propext`,
`Classical.choice`, and `Quot.sound`. No axiom gate has been relaxed.

## Comparison boundaries

The six direct comparisons retain their original contracts, including
callback failure/divergence for `map_err`, arbitrary Default dictionaries
for `take`, zero divisors for ceiling division, and saturation on overflow.
The runner renames only the source metadata for `map_err` to
`map_err_source`, preventing the new backend builtin from suppressing the
body being compared. The full declaration is checked for preservation.

Checked power now contains a power-of-two shortcut and two forms of
exponentiation by squaring. The fresh extraction includes all four generated
loop definitions (the outer branches duplicate the two forms). The proof
compares both loop forms and the shortcut with the bounded mathematical
power for every base and exponent, including zero, overflow, and termination.
It imposes no arithmetic bound or termination premise on the public theorem.

The compiler's `is_val_statically_known` selector is represented by the
universally quantified `milhouse.compiler.StaticKnown` class. Each invocation
queries its U128 base at most once and its U32 exponent at most once. The
queries are in different types and neither is in a loop, so their outcomes
are independent. The runner checks the exact complete caller and all query
sites before introducing the section parameter. Removing that parameter
must reproduce the original generated file byte for byte. No default
instance or axiom is supplied, and no extracted algorithm is replaced.

Three additional numeric helpers are explicit local foundations in
`Tree/CompilerModels.lean`: `u128::ilog2`, `u128::checked_shl`, and
`u128::is_power_of_two`. Their mathematical definitions model the logarithm,
checked shift with truncating machine-word arithmetic, and power-of-two
predicate. **Their Rust implementations are not source-validated by this
suite.** Thus the checked-power result is conditional on those foundation
models, as well as the existing Aeneas checked-multiplication and scalar
models. The new helper boundaries must remain visible when assessing the
compiler trial; Lean axiom-freedom alone does not establish source fidelity.

The runner validates all four external template declarations against their
exact names, signatures, and Rust provenance, then imports the concrete
models. It never compiles an admitted template. Compiler selectors and
numeric foundations are reported separately from direct source comparisons.

## Evidence and native checks

Each run uses a fresh `.lake/core-model-audit/run-*` directory. The report
at `.lake/core-model-audit/report.json` records six direct comparisons, one
parameterized comparison, all four foundation bindings, input hashes,
compiler versions, source spans, and exact theorem axiom dependencies.
A failed run removes the preceding report before starting.

Native tests exercise Default call counts and movement, callback panic
behavior, borrowing and must-use, 24 ceiling-division pairs and three zero
divisors, 35 saturating products, 77 powers, and eight large-exponent cases.
They supplement the universal Lean comparisons; they do not establish
general destructor or unwind behavior, nor which compiler selector outcome
executed. Lean covers both outcomes independently.

The selector tests reject repeated or moved queries, changed branch
conditions, aliased query types, and altered parameter scope. Run the
shared validator tests with:

```sh
python3 -m unittest discover -s scripts -p 'test_aeneas_*.py'
```

The proofs retain Aeneas's reference/value abstraction and its omission of
destructor execution. They are checked separately from the main Tree theorem
inventory. No production Rust or Aeneas source was changed.

## Other numeric diagnostics

`remaining.rs` retains separate diagnostic callers. They are not passing
proof roots. On the September candidate, `usize::pow` fails extraction on
`overflow_checks<bool>` in the new standard-library implementation; its
[separate comparison](../pow_models/README.md) is now a user-approved trusted source model.
The earlier June-pin power comparison remains historical evidence only; the
Pow runner is an optional diagnostic and is excluded from required checks.
`trailing_zeros` and `checked_next_power_of_two` retain additional intrinsic
boundaries. See [the compiler trial status](../../SEPT7_TRIAL_STATUS.md) for
the adoption decision and [upstream limitations](../../UPSTREAM_BUGS.md).
