# Vector model source comparisons

This suite compares the local `Vec::is_empty` and vector equality models with
their pinned standard-library bodies. It also checks the existing foundation
vector inequality model used by local equality. Production Rust, local model
bodies, and Aeneas source are unchanged.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-vec-models.py
```

The shared runner pins Charon 0.1.223, Aeneas `b59d5188`, and
`nightly-2026-06-01`, Rust commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. It checks formatting, runs six native
tests, validates source provenance, generates fresh `VecSource.Types` and
`VecSource.Funs`, and compiles both modules and `CheckModels.lean`. The three
comparison proofs must use only their declared standard Lean axioms.

| Rust body | Comparison and retained foundation |
| --- | --- |
| `Vec::is_empty`, `alloc/src/vec/mod.rs:3085` | Equals the local empty-sequence query for every vector and allocator type. Retains the foundation vector length. |
| Vector `eq`, `alloc/src/vec/partial_eq.rs:15` | Equals `milhouse_models.vec_eq` for all vectors and arbitrary element dictionaries. Actual full-range indexing delegates to the foundation slice comparison, which checks element `ne`. |
| Vector `ne`, `alloc/src/vec/partial_eq.rs:17` | Equals the foundation vector `ne`, including the actual slice trait's inherited negation of equality. |

The comparisons require no element consistency, termination, or successful
lookup premise. Unequal lengths skip all element callbacks. Equal lengths
preserve the first true `ne`, failure, or divergence, leaving later callbacks
unconstrained. The proof relates the slice model's short-circuiting `allM` of
negated answers to the vector model's negated `anyM`, including every `Result`
case. Empty checking uses the vector's existing length bound and imposes no
additional machine-word premise.

The empty-check proof uses `propext`, `Classical.choice`, and `Quot.sound`.
The two comparison proofs use only `propext` and `Quot.sound`. Existing Aeneas
vector/index/slice models remain foundation boundaries: this suite does not
independently prove the slice raw-pointer loop, specialization, heap/allocator
semantics, or destructor behavior. Native tests supplement this limitation.

## Exposing source bodies hidden by builtin matching

Charon produces transparent vector comparison bodies when explicitly including
`alloc::vec::partial_eq`. Aeneas nevertheless selects its registered builtin
definitions by their names. Simply proving something about the generated
callers would therefore compare existing models to themselves. In particular,
the builtin vector equality model calls element `eq`; the corrected local
model intentionally preserves Rust's element `ne` protocol (UPSTREAM_BUGS 17).

The runner first validates the original `alloc::vec` provenance. In a copy of
that LLBC, it changes only the two final function-name identifiers, from `eq`
and `ne` to `eq_source` and `ne_source`. Aeneas then emits their actual bodies.
`check_source_renames` restores those two names in a copy and requires equality
with the **entire original LLBC**. Source code, signatures, function IDs, call
targets, type declarations, trait dictionaries, source spans, and every other
field must remain unchanged. Missing names, collisions, extra declarations,
or any other mutation are errors. The original file is preserved alongside
the renamed input; the report records both name changes.

The six `RangeFull` index operations are included from actual
`core::slice::index` source so their dictionary needs no external templates.
The two generated files must be complete, and the comparisons reference the
newly generated vector definitions explicitly. No code is patched into the
generated Lean and no Aeneas source or builtin registry is changed.

## Native checks and unresolved removal operations

The six tests check:

- Eighteen equality/inequality calls covering all nine pairs of false, true,
  and panicking element `ne` answers, with exact call order and failing `eq`
  sentinels to detect incorrect method substitution.
- Unequal lengths in both directions, empty inputs, and skipped callbacks.
- Empty/nonempty transitions, retained capacity, repeated empty popping, and
  zero-sized elements.
- Owning `pop` without cloning or premature drops, reverse value order, and
  unchanged capacity.
- Mixed front/back iteration without duplicates or premature drops, repeated
  exhaustion, and exact drop counts after the returned elements are released.
- Mixed iteration at zero-sized lengths 0, 1, 2, 7, and 32, plus dropping an
  unfinished iterator while retaining a removed element.

The `pop` and `next_back` callers remain in `source.rs` for native testing and
direct extraction diagnostics. They are not counted as successful source
comparisons. Reproduce their direct extraction from the repository root:

```sh
vec_audit_dir=$(mktemp -d /tmp/milhouse-vec-source-XXXXXX)
../aeneas/charon/bin/charon rustc --preset=aeneas \
  --include 'alloc::vec::_::pop' \
  --include 'alloc::vec::into_iter::_::next_back' \
  --start-from vec_source::pop --start-from vec_source::next_back \
  --dest-file "$vec_audit_dir/vec_source.llbc" -- \
  --edition=2024 --crate-type lib --crate-name vec_source \
  "$PWD/aeneas-lean/reproducers/vec_models/source.rs"
../aeneas/bin/aeneas -backend lean -namespace VecSource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$vec_audit_dir/VecSource" "$vec_audit_dir/vec_source.llbc"
```

Charon succeeds. Aeneas exits 1 at the first container-field accesses:
`Vec`'s `len` at `vec/mod.rs:2851` and `IntoIter`'s `ptr` at
`vec/into_iter.rs:438`. Both report `Unexpected error` from
`llbc/Substitute.ml:202`, which instantiates structure-field types; their bodies
are partial. Adding `--include alloc::vec::Vec` and
`--include alloc::vec::into_iter::IntoIter` to Charon moves the failure to
type analysis of `Vec` (`TypesAnalysis.ml:485`, Rust `vec/mod.rs:438`), followed
by `Not_found` during backward-signature analysis; Aeneas exits 2. These probes
do not establish a Rust bug or a verified replacement for the container models.
No failed/partial output is imported.

## Validation record

Each successful run writes `.lake/vec-model-audit/report.json` after removing
any previous report. It records tool versions, input hashes, original source
spans, the two verified metadata renames, exact axiom dependencies, and the
unresolved `pop`/`next_back` extraction. Nine malformed source inventories,
ten invalid name changes or extra LLBC mutations, and four malformed or
excessive axiom reports were rejected during validation. The existing Option,
core, fixed-byte, and tuple audits also pass with the shared runner extension.

These three standalone comparisons leave the main `Tree` proof and model-root
inventory counts unchanged. Borrowed CoW, remaining numeric and container
boundaries, and the other model/assumption review stay open. Debug and Serde
remain excluded; TreeHash remains deferred.
