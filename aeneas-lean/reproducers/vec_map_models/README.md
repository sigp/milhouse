# VecMap source contracts

This suite checks the pinned `vec_map` 0.8.2 implementation underlying the
default `ProgressiveList` update map, `MaxMap<VecMap<T>>`. It now proves
concrete observers, mutable lookup, and entry acquisition against the actual
slot representation. It does not yet construct a verified concrete
`UpdateMap` dictionary or validate vacant insertion and occupied-entry
consumption.

Run from the repository root with the [project toolchain](../../README.md):

```sh
python3 scripts/aeneas-audit-vec-map-models.py
```

The current pin is Aeneas `7ebd01d`, Charon `85bba1f2` (0.1.251), Rust
`nightly-2026-08-18`, and Lean 4.31.0. The runner checks the pinned compiler,
Miri full-MIR sysroot, locked registry source and source hashes. It runs
formatting and five native tests, then generates fresh `VecMapSource.Types`
and `VecMapSource.Funs`. Both generated files and `CheckModels.lean` must
compile. No generated bodies or LLBC names are changed, and no external
template is accepted or replaced by a local definition.

## Verified source behavior

Nine exact source-body contracts cover seven VecMap methods and the two
actual Option helpers they call:

| Source body | Established behavior |
| --- | --- |
| `VecMap::new` | Zero entry count and an empty slot vector |
| `VecMap::len` | Returns the stored entry count |
| `VecMap::is_empty` | Tests the stored count against zero |
| `VecMap::get` | Indexed slot lookup, with `none` for holes and keys beyond the vector |
| `VecMap::get_mut` | The same lookup and its complete continuation: absent loans preserve the map; present loans update only their slot and retain count metadata |
| `VecMap::contains_key` | Presence of the actual indexed slot, independently of count metadata |
| `VecMap::entry` | Occupied/vacant classification, the exact original map and key, and the full continuation returning a compatible entry's map |
| `Option::as_ref` | Preserves the optional value in the reference abstraction |
| `Option::as_mut` | Absent loans cannot insert; present loans return the replacement, retaining their original value for a missing continuation input |

Seven further theorems establish semantic contracts. `CountMatches` relates
the stored count to occupied slots. Construction establishes it, and every
mutable-lookup continuation preserves it. Under that invariant, length counts
occupied entries and emptiness means every slot is absent. Mutable lookup
needs no count invariant: a missing result restores the whole map, and a
present result changes one slot while preserving count metadata.

The new `vec_map_entry_spec` proves total acquisition, correct occupancy and
key selection, exact map retention, and unchanged release. It needs no count,
clone, allocation, or key-bound premise, including for `usize::MAX`. The entry
contains its actual source map; this proof does not substitute the main
library's abstract vacant-slot footprint for the concrete representation.
`vec_map_entry_eq` also characterizes every continuation input: the original
entry variant returns its replacement map, and an incompatible variant
restores the original map.

All 16 checked proofs use only standard Lean axioms; `option_as_ref_eq` is
axiom-free. The three entry/presence lemmas were added in `1a93d59`. The
runner checks each theorem's axiom dependencies and exact transparent LLBC
source provenance for all nine dependency bodies, including the two helpers'
`core` source crate. Each passing run writes
`.lake/vec-map-model-audit/report.json` with fresh output and input hashes.

The five native tests cover empty and reserved-empty maps, sparse slots,
extreme missing keys, mutation and unchanged release, occupancy counts, and
non-Clone elements. Insertion/removal and occupied entry access are used in
test setup and observations; those calls are not counted as proved bodies.

## Remaining extraction boundaries

The `insert` and `occupied_into_mut` callers remain in `source.rs` for
independent diagnostics. Neither is included in the successful proof roots.

`OccupiedEntry::into_mut` has its own failure, independent of insertion's
iterator dependencies. A fresh full-MIR probe on the current pin has Charon
exit 0 with no LLBC errors, then Aeneas exit 1:

```text
Can't copy a mutable borrow
vec_map-0.8.2/src/lib.rs:684:13-684:21
interp/InterpExpressions.ml:197
```

This is the actual `&mut self.map[index]` expression at the end of the source
method. The generated partial body is rejected and contributes no proof.
Reproduce from the repository root:

```sh
vec_map_probe_dir=$(mktemp -d "$PWD/aeneas-lean/.lake/vec-map-occupied.XXXXXX")
aeneas-lean/.lake/aeneas/charon cargo --preset=aeneas \
  --include vec_map \
  --include 'core::option::_::as_ref' \
  --include 'core::option::_::as_mut' \
  --start-from vec_map_source::occupied_into_mut \
  --dest-file "$vec_map_probe_dir/vec_map_source.llbc" -- \
  --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/vec_map_models/Cargo.toml"
aeneas-lean/.lake/aeneas/aeneas -backend lean -namespace VecMapSource \
  -split-files -filter-trait-methods -no-progress-bar \
  -print-error-emitters -print-error-diagnostics \
  -dest "$vec_map_probe_dir/VecMapSource" "$vec_map_probe_dir/vec_map_source.llbc"
```

The diagnostic requires the same full-MIR sysroot as the successful suite;
a fallback to rustc's default sysroot is not acceptable evidence. Session logs,
source hashes, and per-stage statuses are retained under
`.lake/cow-concrete-map-probe/occupied/`.

For insertion, including only `vec_map` leaves templates for `Iterator::map`,
map-iterator `next`, and `Vec::extend`. Including the actual iterator/extension
dependencies instead fails on `try_fold` signatures. Both filtered and
unfiltered September compiler probes fail; see the
[compiler diagnostic matrix](../compiler_workarounds/README.md). No additional
models replace these dependencies.

## Validation boundaries

The main library separately proves the actual MaxMap wrapper's callback
composition and its high-level CoW contracts over selected inner-map laws.
See [the current CoW status](../../COW_PROOFS_STATUS.md). These standalone
VecMap contracts advance concrete source fidelity, but do not yet discharge
all of those laws or prove the local vacant-entry footprint's full refinement.
Range/max queries and a complete concrete map dictionary remain open too.

The proofs retain Aeneas's vector allocation/size, indexing, scalar, and
reference foundations. They do not verify allocator behavior, raw pointers,
destructors, or every construction of a valid VecMap. The standalone modules
remain outside `Tree`; the main theorem and included-root model inventories
are unchanged. The approved `usize::pow` source assumption is unchanged.
