# VecMap source contracts

The September 7 migration retains all 13 proofs in this suite. Use the
[project toolchain setup](../../README.md) and the pinned defaults of its
audit command. Earlier compiler pins, source locations, and checkpoint
counts below are historical; current versions and input hashes are recorded
in each new audit report. The temporary `usize::pow` assumption does not
exclude any proof in this suite.

This suite checks the pinned `vec_map` 0.8.2 implementation underlying the
default `ProgressiveList` update map, `MaxMap<VecMap<T>>`. It proves concrete
observer and mutable-lookup behavior against slot semantics. It does not yet
construct a verified `UpdateMap` dictionary or validate insertion, range
iteration, maximum queries, or `MaxMap` composition.

The main library separately extracts and proves `MaxMap` default, lookup,
insertion, cardinality, and cached-maximum behavior over an abstract inner
`UpdateMap`, including preservation of cache validity. See
[the wrapper source proofs](../../PROGRESSIVE_LIST_MODEL_AUDIT.md#maxmap-wrapper-source-proofs).
Connecting this suite's concrete VecMap representation to that dictionary
remains unfinished.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-vec-map-models.py
```

The shared runner pins Charon 0.1.223, Aeneas `b59d5188`, and Rust
`nightly-2026-06-01` (commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`).
It verifies the locked registry dependency, hashes its source, runs formatting
and four native tests, and generates fresh `VecMapSource.Types` and
`VecMapSource.Funs`. Both generated files and `CheckModels.lean` must compile.
No LLBC names or generated bodies are changed, and no external template is
accepted or replaced by a local definition.

Seven exact source equations cover five VecMap methods and the two actual
Option helpers they call:

| Source body | Proved behavior |
| --- | --- |
| `VecMap::new`, `vec_map/src/lib.rs:118` | Zero entry count and an empty slot vector |
| `VecMap::len`, line 428 | Returns the stored entry count |
| `VecMap::is_empty`, line 444 | Tests the stored count against zero |
| `VecMap::get`, line 474 | Returns the indexed slot, with `none` for holes or keys beyond the slot vector |
| `VecMap::get_mut`, line 513 | Returns that same optional value and the exact continuation: absent loans preserve the whole map; present loans update only their slot and retain count metadata |
| `Option::as_ref`, `core/src/option.rs:741` | Preserves the optional value in the reference abstraction |
| `Option::as_mut`, line 763 | An absent loan cannot insert; a present loan returns the supplied replacement, retaining its old value for a missing continuation input |

Six further theorems establish the semantic contracts. `CountMatches` relates
the stored entry count to the number of occupied vector slots. Construction
establishes it; every continuation from actual mutable lookup preserves it.
Under this invariant, length counts occupied entries and emptiness is
equivalent to every slot being absent. Mutable lookup needs no count invariant:
a missing result restores the entire map, and a present result changes exactly
one slot while preserving count metadata. The lookup equations quantify over
arbitrary element types and all machine-word keys without cloning, count
invariants, successful-call premises, or supplied bounds. The derived observer
and preservation lemmas explicitly state the count invariant and successful
immutable-read or mutable-call premises they use.

The thirteen checked proofs use only standard Lean axioms; `option_as_ref_eq`
is axiom-free. The runner checks each theorem's axiom dependencies. It also
checks exact transparent LLBC source provenance for all seven dependency
bodies, including the two helpers' distinct `core` source crate. Four Python
tests in `scripts/test_aeneas_source_crates.py` check the mixed-crate validation,
preserve legacy single-crate checking, and reject incorrect crate/path/body/
transparency/locality metadata and unused overrides. The eight existing source
suites also pass with this extension.

The four native tests cover empty and reserved-empty maps, sparse slots,
extreme missing keys including `usize::MAX`, in-place replacement, unchanged
other slots/counts, and a non-Clone element type. Native insertion/removal is
used to build test states; these calls are not counted as proved source bodies.

## Insertion extraction boundary

The `insert` caller is retained in `source.rs`, but excluded from the successful
proof suite. Including only `vec_map` leaves external templates for
`Iterator::map`, map-iterator `next`, and `Vec::extend`. No proof substitutes a
new model for these calls. Including their iterator/extension dependencies
instead exposes unsupported `try_fold` signatures and a bound-region failure.
Reproduce that diagnostic from the repository root:

```sh
vec_map_probe_dir=$(mktemp -d /tmp/milhouse-vec-map-insert-XXXXXX)
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include vec_map \
  --include 'core::iter::traits::iterator::Iterator::map' \
  --include 'core::iter::adapters::map' \
  --include 'alloc::vec::_::extend' \
  --start-from vec_map_source::insert \
  --dest-file "$vec_map_probe_dir/vec_map_source.llbc" -- \
  --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/vec_map_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace VecMapSource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$vec_map_probe_dir/VecMapSource" "$vec_map_probe_dir/vec_map_source.llbc"
```

Charon succeeds. Aeneas exits 2: `Iterator::try_fold` and the map adapter's
`try_fold` fail at `symbolic/SymbolicToPureTypes.ml:1012`;
`map_try_fold` also reports `Unexpected erased region` at line 813. The source
locations are `core/src/iter/traits/iterator.rs:2486` and
`core/src/iter/adapters/map.rs:91,115`. This probe does not establish a Rust bug
or a general impossibility result for other extraction strategies.
No partial output is imported and Aeneas is unchanged. See UPSTREAM_BUGS 28.

## Validation boundaries

Each passing run writes `.lake/vec-map-model-audit/report.json`, removing any
old report first. Its seven `directSourceComparisons` entries are concrete
source contracts, not comparisons with pre-existing production VecMap models.
`validatedProofs` also includes the six derived invariant/specification lemmas.
The report records fresh output, source and input hashes, exact axiom use,
and the unresolved insertion/concrete-map obligations.

The proofs retain Aeneas's vector allocation/size, indexing, scalar, and
reference foundations. They do not verify allocator behavior, raw pointers,
destructor execution, or all ways of constructing a valid VecMap. These
standalone modules are outside `Tree`; the main theorem and included-root
model inventories are unchanged. The existing vacant-entry footprints and
generic UpdateMap laws are not replaced or discharged by this suite alone.
