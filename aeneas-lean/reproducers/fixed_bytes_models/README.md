# Fixed-byte cache model source comparisons

This suite compares the five reached `FixedBytes` models with the actual
`alloy-primitives` 1.0.0 bodies used for cache initialization and rebasing.
The Rust callers invoke the dependency's methods and constant directly. A
separate Cargo manifest pins the dependency, uses its default features, and
keeps the complete dependency lockfile. Production Rust and local models are
unchanged.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-fixed-bytes-models.py
```

The shared source-audit runner checks Charon 0.1.223, Aeneas `b59d5188`, and
`nightly-2026-06-01` Rust commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. Cargo runs with `--offline --locked`.
After checking formatting and running the four native tests, Charon includes
`alloy_primitives::bits::fixed` from the five caller roots. Aeneas generates
fresh `FixedSource.Types` and `FixedSource.Funs`; both modules and
`CheckModels.lean` must compile.

| Comparison | Verified behavior |
| --- | --- |
| Derived `clone` | Preserves the entire byte array. The comparison is axiom-free. |
| `ZERO` | The extracted constant, lifted into `Result`, equals the local zero constructor at every length. |
| `Default::default` | Delegates to the actual zero constant and matches the local default model. |
| Derived `eq` | The actual array-comparison call equals the local equality of byte lists for every pair of arrays. |
| `is_zero` | Equality with the actual zero constant equals the local all-bytes-zero check. |

All comparisons quantify over every machine-word array length and every
array of that length, including length zero. They impose no byte, size, or
callback premise. The last four comparisons use only `propext`,
`Classical.choice`, and `Quot.sound`. The extracted newtype reduces to the
same Aeneas array type used locally; equality retains Aeneas's existing
array/slice comparison and byte comparison foundation. These are not proofs
of those foundation implementations or compiler/heap semantics.

The source check requires transparent nonlocal bodies from
`alloy-primitives-1.0.0/src/bits/fixed.rs`: derived clone at line 16, derived
equality at line 18, default at line 41, the zero constant at line 337, and
`is_zero` at line 581. For `ZERO`, it also verifies that the global declaration
and its initializer agree and that the constant calls the inspected body.
Missing/external templates and admitted generated code are rejected.

Each successful fresh run writes `.lake/fixed-bytes-model-audit/report.json`
after validation. The report records tool versions,
source spans, exact axiom dependencies, local source/manifest/lockfile hashes,
and the dependency source-file hash. As in the other suites, the old report is
removed before work begins, so a failed run cannot leave a stale passing report.
The inspected dependency file hash is
`232ff9e82e4a41e89c54947aeb870fc1c9c3ec886ff670d96fea881c9054e917`.

The native tests cover zero/default at lengths 0, 1, 31, 32, 33, and 64;
cloning a patterned cache without changing its original; equality after a
change at each of the 32 cache-byte positions; and the zero check with each
of the 256 cache bits set individually. They supplement the universal Lean
equalities.

The real extracted inventory and all five axiom reports pass. Eleven malformed
inventories are rejected, including a wrong dependency/version path, local
replacement, missing body, and mismatched constant/initializer links. Four
malformed axiom reports are rejected, including an admission, a missing or
duplicate comparison, and an added axiom in the clone proof. The existing
core and Option suites also pass after the shared runner extension.

These five checks have their own compilation/axiom gate outside `Tree`.
They leave the main library's 5,015 declarations across 314 modules and the
42-root/151-declaration dependency inventory unchanged. The full library gate
was not repeated for these standalone checks. Borrowed CoW, the three numeric
intrinsic boundaries, and the remaining model/assumption review stay open.
