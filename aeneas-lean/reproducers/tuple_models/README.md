# Tuple comparison model source comparisons

The September 7 migration retains all 4 proofs in this suite. Use the
[project toolchain setup](../../README.md) and the pinned defaults of its
audit command. Earlier compiler pins, source locations, and checkpoint
counts below are historical; current versions and input hashes are recorded
in each new audit report. The temporary `usize::pow` assumption does not
exclude any proof in this suite.

This suite compares the four local pair-comparison models with the actual
standard-library bodies in `core/src/tuple.rs`. Its generic Rust callers
select tuple `eq`, `ne`, `partial_cmp`, and `cmp` directly. Production Rust,
local models, and Aeneas source are unchanged.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-tuple-models.py
```

The shared runner pins Charon 0.1.223, Aeneas `b59d5188`, and Rust
`nightly-2026-06-01` commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. It checks formatting, runs the four
native tests, extracts fresh `TupleSource.Types` and `TupleSource.Funs`, and
compiles both generated modules and `CheckModels.lean`. The provenance gate
requires transparent nonlocal bodies from `/rustc/library/core/src/tuple.rs`,
at lines 30, 34, 69, and 114 respectively. It selects the `core::tuple` module
explicitly, distinguishing these bodies from identically named trait defaults
or reference implementations.

| Comparison | Behavior preserved |
| --- | --- |
| `eq` | Calls first element `eq`; only a true result reaches second element `eq`. |
| `ne` | Calls first element `ne`; only a false result reaches second element `ne`. |
| `partial_cmp` | Only `Some(Equal)` reaches the second comparison; `None`, `Less`, and `Greater` short-circuit. |
| `cmp` | Only `Equal` reaches the second comparison. |

All four Lean equalities quantify over arbitrary element types, values, and
callback dictionaries, preserving failure and divergence as well as successful
results. No callback-coherence, success, or termination premise is required.
The `eq` and `ne` comparisons are axiom-free. The two ordering comparisons
use only `propext`, which their existing local model definitions already use.
These are comparisons within Aeneas's reference/value abstraction, not proofs
of compiler or heap semantics. Destructor execution remains unmodeled.

The native tests exercise all 59 combinations of first and second answers:
nine each for equality and inequality, 25 for partial ordering, and 16 for
total ordering. Each includes panicking callbacks. They check results, exact
method selection, and left-to-right call order, including skipped panics.
Other comparison methods record a distinct call and panic, detecting any
unjustified substitution between `eq`, `ne`, `partial_cmp`, and `cmp`.

## Unused trait defaults

Including `core::tuple` also discovers four newer standard-library defaults:
`core::cmp::PartialOrd::__chaining_lt`, `__chaining_le`, `__chaining_gt`, and
`__chaining_ge`. The pinned Aeneas `PartialOrd` dictionary lacks these fields.
An unfiltered Aeneas run emits four external templates, despite exiting zero.
Adding `--include core::cmp` instead fails with `Arrow types are not supported
yet` in their function-pointer adapters at `cmp.rs` lines 1479, 1487, 1495,
and 1503. No partial or template output is imported.

These helpers serve other ordering methods and are not called by the four
compared bodies. The runner first extracts the unfiltered LLBC, then reruns
Charon with exactly these four defaults excluded. Both inventories must pass
the source provenance gate, and all four complete source declarations must
be identical between runs. `--no-dedup-serialized-ast` ensures this compares
expanded declarations rather than references into different serialization
tables. This check would reject any change to a compared body or signature.
The selected extraction must produce exactly the two complete Lean modules;
missing methods, external templates, and admissions remain errors.

Aeneas still warns about the four missing dictionary fields. This does not
establish correctness of the entire `PartialOrd` interface or tuple
`lt`/`le`/`gt`/`ge`; the checked scope is the four listed methods. No Aeneas
modification or replacement callback is needed for them.

## Validation record

Successful runs write `.lake/tuple-model-audit/report.json` with tool versions,
input hashes, source spans, the four exclusions and unchanged declarations,
and exact axiom dependencies. The old report is removed before work starts.
Nine malformed source inventories, a changed comparison body after exclusions,
and four malformed or excessive axiom reports were rejected during validation.
The existing Option, core, and fixed-byte suites also pass with the shared
runner extension.

These four comparisons have a separate compilation/axiom gate outside `Tree`.
They leave the main proof and dependency inventory counts unchanged. The
ProgressiveList inventory reaches this tuple dictionary through BTreeMap
lookup for optional hashes; existing branch proofs show the included progressive update
path passes `None` and skips that lookup. The earlier
[inequality regression](../tuple_comparison/README.md) remains useful historical
evidence for the corrected `ne` model. Borrowed CoW, remaining numeric/container
boundaries, and other model/assumption review remain open. Debug and Serde are
excluded, and TreeHash remains deferred.
