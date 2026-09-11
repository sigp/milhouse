# September compiler workaround probes

These diagnostics retest possible reversions of the Rust extraction workarounds
with the official compiler pinned in `aeneas-toolchain.json`. They also reuse
the existing Option, borrowed-CoW, and VecMap source reproducers. They do not
modify Aeneas, production Rust, external models, or the proof library.

After installing the [project toolchain](../../README.md), run from `aeneas-lean`:

```sh
lake env python3 reproducers/compiler_workarounds/probe.py
```

The runner checks the compiler versions and rejects a fallback from Miri's
full-MIR sysroot. It creates a fresh directory under
`.lake/compiler-workaround-probes/` and records per-stage exit codes, tool
versions, and source hashes in `report.json`. Extraction errors are expected:
the runner finishing with exit zero means the diagnostics completed, not that
the probed methods are verified. Missing stages were not run. In particular,
external templates are never filled with assumptions or imported into Lean.
No partial generated output enters the production library.
Charon can exit zero after reporting a transformation type error; the report
records `charonTypeError` and `llbcHasErrors` separately from its process status.

## Observed on September 11, 2026

Aeneas `7ebd01d`, Charon `85bba1f2` (0.1.251), Rust
`nightly-2026-08-18`, and Lean 4.31.0:

| Case | Result | Consequence |
| --- | --- | --- |
| `record_insert`: restore `(*max_index).max(index)` | Charon and Aeneas exit 0; generated Lean fails because `Ord.max.default` receives an Ord dictionary instead of a comparison function | Keep the explicit maximum comparison |
| `take`: consume an option carrying a mutable metadata reference | Aeneas exits 1 with `Unreachable` during value translation | The tested borrowed `Option::take` spelling is still unsupported |
| `borrowed_try`: use `?` on `Option<&mut u32>` | Extraction emits external templates; the caller expects a backward continuation absent from the template signature | Keep the explicit matches in MaxMap's borrowed wrappers |
| `fallback`: borrowed lazy `or_else` closure | Aeneas exits 1: cannot end a non-endable abstraction | Keep the explicit lazy lookup branches |
| `use_cloned`: cloned slice iterator alongside a non-reference Counter iterator | Charon reports an associated-type trait-clause mismatch despite exiting 0; Aeneas exits 2 during signature translation | Keep the Iterator cloning-adapter workarounds |
| `into_iter`: loop over a generic IntoIterator input | Aeneas exits 1: missing input type variable during extraction | Keep the Iterator-only builder helper |
| `fnmut`: closure mutating its captured reference | Generated Lean fails its FnOnce/FnMut calling conventions | Keep the closure-free packed-leaf update |
| Actual `Option::cloned` source | Aeneas exits 1 on bound-region/function-item translation | Keep the existing composition proof; direct source extraction remains unresolved |
| All borrowed-CoW enum readers | Aeneas exits 1 on all eight readers in `lookup_loan` | Lifetime separation and the tested helper/copy spellings still do not unblock borrowed CoW |
| Actual VecMap insertion dependencies | Aeneas exits 2 on `try_fold` signatures, both with and without `-filter-trait-methods` | Concrete insertion and full VecMap dictionary fidelity remain unfinished |

The `take` fixture is a small function over a borrowed option, not an
extraction of the complete `CowOnMut::run` method. The other small fixtures
similarly isolate language patterns; the Option, CoW, and VecMap cases reuse
their separate source suites. These failures do not prove that every possible
alternative spelling is unsupported.

## Successful production changes

Separate full-production extraction demonstrated two useful improvements:

- `-filter-trait-methods` removes unsupported `size_hint` and `rev` dictionary
  fields. Both `to_vec` methods and the progressive rebuilding helper now use
  ordinary Rust `for` loops. Their existing proofs were adapted to the new
  generated loop-state order; their semantic assumptions are unchanged.
- The provided `UpdateMap::is_empty` body and its concrete MaxMap caller now
  extract and compile, including the full wrapper dictionary. Seven new
  source/observer lemmas derive emptiness from inner length without a separate
  emptiness-answer premise for that dictionary. They use only standard Lean
  axioms. Arbitrary map overrides retain their own contracts.

These changes are in `da402d9` and `2356f2c`. The mathematical clone, equality,
hash, packing, and representation requirements do not disappear merely because
the compiler supports more syntax. The approved `usize::pow` source assumption
is unchanged. Debug and Serde remain out of scope; TreeHash remains deferred.
