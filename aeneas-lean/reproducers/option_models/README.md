# Option model source comparison

This check explicitly includes the pinned Rust standard library's Option
method bodies in Charon, extracts them into an independent Lean namespace,
and compares them with the local definitions in `Tree/FunsExternal.lean`.
The Rust file calls the actual standard-library methods; it does not copy
their implementations or replace any milhouse method.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-option-models.py
```

The script builds `Tree.FunsExternal`, checks Rust formatting, runs two native
clone-protocol tests, and regenerates all directly compared methods. It checks
that each required LLBC body is transparent, belongs to `core`, and originates
in `/rustc/library/core/src/option.rs`. It rejects extraction errors, missing
bodies, external model templates, admissions, opaque declarations, or missing
axiom reports. Generated output, compilation logs, source hashes, versions,
and the final report are retained in `.lake/option-model-audit/`. Each run uses
a fresh directory and removes the previous report before starting.

The check pins Charon 0.1.223, Aeneas `b59d5188`, and Rust
`nightly-2026-06-01` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). The recorded
Charon checkout is `cb50ff16b9f1066b8a97dc06da704de2da2fa41c` and Aeneas checkout
is `b59d5188c082f704a418c7cb4e52ad69328002d1`. `--charon`, `--aeneas`, or the
corresponding uppercase environment variables select executable paths;
unexpected reported versions fail the check.

## Verified comparisons

All twelve lemmas in `CheckModels.lean` validate **without axioms**. Eleven
compare the entire actual extracted standard-library function with its local
model, for all inputs and callback dictionaries:

- `is_some_and`, `is_none_or`, `map`, and `map_or` preserve branch selection,
  skipped callbacks, and arbitrary callback results, including failure/divergence.
- `unwrap_or_default` preserves the actual default call and its skipped branch.
- `ok_or`, `or`, `unzip`, and shared-reference `copied` preserve their values.
- `Try::branch` and `FromResidual::from_residual` preserve control flow.
  The generated residual body's impossible `Some Infallible` branch is
  eliminated using the empty type, without an assumption about residuals.

These are equalities in Aeneas's value/reference abstraction with destructor
execution omitted. They do not establish arbitrary destructor effects or a
refinement proof for the compiler/Aeneas pipeline. The generated modules and
checks live outside the main `Tree` library and have their own compilation and
axiom gate; they are not added to its theorem count.

## `cloned`: composition verified, direct extraction unresolved

The twelfth lemma checks the pinned source's `self.map(T::clone)` composition:
the fully extracted `map` body, given the actual clone callback, equals the
local `cloned` model. It requires no terminating or identity-clone law. The
native tests confirm a nonidentity clone is called once, absence skips cloning,
and a clone panic propagates without changing the original value.

Direct extraction of the standard-library `cloned` body still fails at
`llbc/RegionsHierarchy.ml:180`: the `T::clone` function item has locally bound
regions that Aeneas does not support there. The composition theorem is not
counted as a successful direct extraction. The report records this distinction.

To reproduce that failure from this directory:

```sh
probe_output=$(mktemp -d /tmp/milhouse-option-cloned-XXXXXX)
"$CHARON" rustc --preset=aeneas --include core::option \
  --dest-file "$probe_output/option_source.llbc" -- \
  --edition=2024 --crate-type lib --crate-name option_source source.rs
"$AENEAS" -backend lean -namespace OptionSource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$probe_output/OptionSource" "$probe_output/option_source.llbc"
```

Charon succeeds; Aeneas exits 1 and emits a partial `cloned` body. The audit
instead selects the eleven supported roots explicitly and never imports that
partial output. The recorded full probe is
`/tmp/milhouse-option-source-lipy_vu4/`, with `aeneas-all.log` containing the
failure. No Aeneas source or production model was changed.

Validator checks also rejected seven malformed inputs: LLBC error status,
wrong Charon version, opaque body, local replacement, missing source method,
missing axiom report, and duplicate axiom reports.
