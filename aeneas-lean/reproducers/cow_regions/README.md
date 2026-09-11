# Borrowed CoW reference-layout reproducer

This dependency-free crate isolates the shared-reference failure affecting
borrowed CoW reads. It tests whether separating the backing-value and mutable
entry lifetimes helps, without changing production types or methods.

## September compiler controls

The four existing control proofs are required by the September 7 compiler
migration. The eight failing enum-reader results below are historical
June-pin diagnostics; no new support for those methods is claimed.
After following the [toolchain setup](../../README.md), run these commands
from the repository root to extract and validate the controls:

```sh
cow_probe=$(mktemp -d /tmp/milhouse-cow-controls-XXXXXX)
cargo +nightly-2026-08-18 test --locked --offline \
  --manifest-path aeneas-lean/reproducers/cow_regions/Cargo.toml
cargo +nightly-2026-08-18 fmt --check \
  --manifest-path aeneas-lean/reproducers/cow_regions/Cargo.toml
aeneas-lean/.lake/aeneas/charon cargo --preset=aeneas \
  --start-from milhouse_cow_regions_probe::read_plain \
  --start-from milhouse_cow_regions_probe::read_nested \
  --start-from milhouse_cow_regions_probe::read_shared_field \
  --start-from milhouse_cow_regions_probe::read_unique_field \
  --dest-file "$cow_probe/controls_only.llbc" -- --locked --offline \
  --manifest-path aeneas-lean/reproducers/cow_regions/Cargo.toml
aeneas-lean/.lake/aeneas/aeneas -backend lean -split-files -no-progress-bar \
  -dest "$cow_probe/ControlsOnly" "$cow_probe/controls_only.llbc"
(
  cd aeneas-lean
  lake env python3 reproducers/cow_regions/check_controls.py "$cow_probe"
)
```

The source comparison for `usize::pow` is the only deferred proof in this
compiler upgrade; that assumption does not apply to these four control lemmas.

## Observed boundary

With Aeneas `b59d5188c082`, Charon `cb50ff16b9f1` (LLBC 0.1.223), and
`nightly-2026-06-01`, native Rust reads succeed for every tested branch and leave
the backing and pending values unchanged. Charon translates the whole crate.

| Functions | Aeneas result |
| --- | --- |
| `read_plain`, `read_nested` | Complete bodies returning the supplied value |
| `read_shared_field`, `read_unique_field` | Complete bodies returning the struct's field |
| `read_one`, `read_split` | Fail at the enum's shared-reference branch |
| `read_one_entry`, `read_split_entry` | Same failure with an optional mutable entry slot |
| `read_one_via_helper`, `read_one_entry_via_helper` | Same failure despite calling the working nested-reference helper |
| `read_one_by_copy`, `read_one_entry_by_copy` | Same failure when the pattern copies the shared reference directly and borrows only the mutable variant |

All eight failing bodies report `Unreachable` from
`interp/InterpBorrowsCore.ml:629` (`lookup_loan`); `interp/Interp.ml:609`
reports the enclosing translation failure. Aeneas exits with status 1 and
emits partial files with `sorry` bodies for those methods. These are failed
translations, and no partial output is imported into the production library.

The result rules out lifetime separation, removal of map/entry dependencies,
the nested-reference helper, and the tested direct-copy patterns as solutions
to these examples. It does not claim that every possible enum representation
or rewrite is unsupported. Plain and single-field controls distinguish this
failure from a general inability to read through nested references.

This crate does not implement a real map or replace any milhouse method.
It does not prove `Cow::deref`, `Cow::make_mut`, or `next_cow`. The production
borrowed methods remain unproved, and Aeneas sources are unchanged.

## Reproduce

From this directory, set `CHARON` and `AENEAS` to the built executables:

```sh
probe_output=$(mktemp -d /tmp/milhouse-cow-regions-XXXXXX)
cargo +nightly-2026-06-01 test --locked --offline
cargo +nightly-2026-06-01 fmt --check
"$CHARON" cargo --preset=aeneas \
  --start-from milhouse_cow_regions_probe \
  --dest-file "$probe_output/probe.llbc" -- --locked --offline
"$AENEAS" -backend lean -split-files -no-progress-bar \
  -print-error-emitters -print-error-diagnostics \
  -dest "$probe_output/partial/Probe" "$probe_output/probe.llbc"
```

The final command is expected to fail on the eight enum readers above.
For successful controls, extract only their concrete roots into separate files:

```sh
"$CHARON" cargo --preset=aeneas \
  --start-from milhouse_cow_regions_probe::read_plain \
  --start-from milhouse_cow_regions_probe::read_nested \
  --start-from milhouse_cow_regions_probe::read_shared_field \
  --start-from milhouse_cow_regions_probe::read_unique_field \
  --dest-file "$probe_output/controls_only.llbc" -- --locked --offline
"$AENEAS" -backend lean -split-files -no-progress-bar \
  -dest "$probe_output/clean/ControlsOnly" "$probe_output/controls_only.llbc"
cd ../..
lake env python3 reproducers/cow_regions/check_controls.py "$probe_output/clean"
```

The checker compiles the separately generated control types and bodies and
the four lemmas in `CheckControls.lean`, then checks their axiom reports.
All four proofs validate with no axioms. It uses the existing Lean project's
built dependencies and writes only inside the supplied output directory.
The control-only extraction has no failed bodies or external model templates.

The recorded run used `/tmp/milhouse-cow-regions-fv7auM/`:
`aeneas-by-copy.log` contains the final eight failures, while
`aeneas-controls-only.log` and `clean/` contain the successful control extraction
and checked Lean output. Native tests and formatting pass for the final source.
