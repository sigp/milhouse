# Core model source comparisons

This check compares the local `mem::take` and `usize::div_ceil` models with
fresh extraction of their actual pinned Rust standard-library bodies. The
Rust file calls those methods and contains native protocol tests; it does not
copy either implementation or replace a milhouse operation.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-core-models.py
```

The runner builds `Tree.FunsExternal`, checks Rust formatting, runs four native
tests, extracts the two standard-library bodies into `CoreSource`, checks their
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
division and requires `take` to be axiom-free.

## Verified behavior

| Comparison | Result |
| --- | --- |
| `mem::take` | Equal to the actual body from `core/src/mem/mod.rs:849`, for any value and Default dictionary, including default failure/divergence. Success returns the old value and installs the returned default in the modeled place. The proof is axiom-free. |
| `usize::div_ceil` | Equal to the actual body from `core/src/num/uint_macros.rs:3755` for all machine-word inputs, including zero divisors. The proof uses only `propext`, `Classical.choice`, and `Quot.sound`; it assumes no positivity or size bound. |

The ceiling-division proof follows Rust's quotient, remainder, and conditional
increment. A nonzero remainder implies both a positive dividend and divisor
greater than one, so rounding remains bounded by the dividend. This proves the
increment cannot introduce an extra overflow case in the local model.

The native tests check that successful `take` calls Default once, moves the
old value without dropping it, and places the default value in its slot. A
panicking Default leaves the tested original value intact and undropped.
Ceiling division is checked at 24 combinations including `usize::MAX`, plus
three zero-divisor cases. These native checks supplement the universal Lean
equalities; they are not universal panic-state or destructor proofs.

The checker rejects missing or opaque source bodies, incorrect source paths,
partial extraction, and unexpected axiom dependencies. Eleven malformed
inventory/report inputs were rejected, including a null structured body and
an injected axiom in the `take` theorem. The Option suite also rejected an
injected `propext` dependency after moving to the shared runner.

Both methods extract completely. The comparisons still trust Aeneas's
reference/value abstraction and its foundation models, including `mem::replace`
and scalar arithmetic. Destructor execution is omitted by extraction; the
native tests observe only their specified concrete cases. No Aeneas source,
production Rust, or local model body changed. These generated modules have a
separate compilation/axiom gate outside the main `Tree` library and do not
increase its theorem count.
