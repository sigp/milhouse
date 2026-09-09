# Arbitrary control model source comparison

Run from the repository root:

```sh
python3 scripts/aeneas-audit-arbitrary-models.py
```

The suite compares `milhouse.arbitrary.nextControl` with the actual
`bool::arbitrary` implementation from pinned `arbitrary` 1.4.1. It includes
the actual `u8::arbitrary` and `Unstructured::fill_buffer` bodies, including
the zero-fill iterator loop. No generator implementation is substituted.

The shared runner pins Charon 0.1.223, Aeneas `b59d5188`, and
`nightly-2026-06-01` (Rust commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). It checks formatting, runs seven
native tests, validates original dependency provenance, generates complete
Lean files, and compiles them with `CheckModels.lean`. `control_agrees` uses
only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved behavior

The comparison covers every input slice and both outputs: the Boolean result
and exact remaining input. An available byte is consumed, including an even
byte that stops collection. At exhaustion, the read succeeds with false and
retains the empty input. No input-length, read-success, or termination premise
is imposed.

The proof follows these source operations:

- `bool::arbitrary`, `src/foreign/core/bool.rs:4`, calls the actual byte
  generator and tests its low bit. The proof relates the bitwise test to the
  local model's remainder modulo two.
- `u8::arbitrary`, `src/foreign/core/num.rs:16`, fills its one-byte array and
  converts that array from little endian. All success/error branches remain
  in the extracted body.
- `Unstructured::fill_buffer`, `src/unstructured.rs:558`, copies the available
  prefix, zero-fills the remainder, and advances the input. The helper theorem
  covers every input and initial byte for the **one-byte buffer used by this
  path**; it is not a general buffer-width theorem. It proves termination and
  the actual mutable-iterator write-back in both exhaustion cases.

The source `Unstructured` is extracted as its real single-field structure;
the comparison maps that field to the local slice representation. The three
source error variants are mapped individually. Existing Aeneas array, slice,
copy/index, mutable-iterator, scalar ordering/bitwise, and Result models remain
foundation boundaries. No independent raw-memory or allocator proof is claimed.

The function provenance filter selects `arbitrary::foreign::core::bool`, so
the identically named byte-generator method cannot be mistaken for the bool
method being compared. Type provenance is checked separately against the
dependency crate. The generated `Error` discriminant instance otherwise
collides with `Tree.Types` as `instDiscriminantErrorIsize`. The runner changes
only the source type's final metadata name to `SourceError`, then verifies
that restoring it recovers the **entire original LLBC**. Source bodies,
signatures, fields, IDs, calls, dictionaries, and spans must remain unchanged.
The original input is preserved as `original-metadata.llbc`.

## Native coverage and remaining source boundaries

The seven tests cover all 256 control-byte values and repeated exhaustion;
768 one-byte buffer overwrites; even stopping-byte consumption; exact input
after the first element error; generator input replacement that produces two
elements from a one-byte initial input; panic short-circuiting; the owning
trait default's ordinary-generator dispatch; and both size-hint defaults,
including a custom hint and maximum depth. These checks supplement the source
comparison. Full vector generation and the three trait defaults are not yet
counted as verified source comparisons.

The owning default fails direct extraction with the real `Unstructured` type.
Reproduce from the repository root:

```sh
arbitrary_audit_dir=$(mktemp -d /tmp/milhouse-arbitrary-source-XXXXXX)
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include arbitrary::Arbitrary --include arbitrary::unstructured::Unstructured \
  --include arbitrary::error::Error --include arbitrary::MaxRecursionReached \
  --start-from arbitrary_source::take_rest \
  --start-from arbitrary_source::size_hint --start-from arbitrary_source::try_size_hint \
  --dest-file "$arbitrary_audit_dir/defaults.llbc" -- --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/arbitrary_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace ArbitrarySource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$arbitrary_audit_dir/Defaults" "$arbitrary_audit_dir/defaults.llbc"
```

Charon succeeds. Aeneas exits 1: `Can not end a borrow because the value to
give back contains bottom` at `lib.rs:216` (`InterpBorrows.ml:358`, followed
by `Interp.ml:609`). The size-hint bodies are emitted in this partial module;
that output is not imported. Its generic trait declaration also has the known
namespace shadowing described in `scripts/aeneas-qualify-arbitrary.py`.

The full vector caller has additional iterator limitations:

```sh
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include arbitrary::foreign::alloc::vec --include arbitrary::unstructured \
  --include arbitrary::Arbitrary --include arbitrary::error::Error \
  --include arbitrary::MaxRecursionReached --start-from arbitrary_source::vector \
  --dest-file "$arbitrary_audit_dir/vector.llbc" -- --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/arbitrary_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace ArbitrarySource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$arbitrary_audit_dir/Vector" "$arbitrary_audit_dir/vector.llbc"
```

Charon succeeds; Aeneas exits 1. `ArbitraryIter::next` reports `Can't copy a
mutable borrow` at `unstructured.rs:758` (`InterpExpressions.ml:197`). The
generic `Unstructured::arbitrary` helper has the same borrow-ending error as
the owning default. `Vec::arbitrary` reports an internal error at
`foreign/alloc/vec.rs:10` (`InterpBorrowsCore.ml:1498`), and `arbitrary_iter`
reports `Unimplemented` at `unstructured.rs:643`
(`SymbolicToPureExpressions.ml:1157`). The foundation Iterator dictionary also
lacks `collect`. No partial output or external template is used in the proof.
These findings establish extraction limitations, not a Rust bug.

Successful runs write `.lake/arbitrary-model-audit/report.json`, recording
tool pins, dependency/input hashes, original spans, checked metadata rename,
and exact axiom dependencies. A previous report is removed before each run.
Validation rejected ten malformed source inventories, ten invalid metadata
or type-namespace cases, and four invalid axiom reports. All six existing
source-comparison suites also pass with the shared runner change. The main
proof library and model-root inventory are unchanged; their gates were not
repeated for this standalone audit. Remaining Arbitrary/model boundaries,
borrowed CoW, and the assumption review stay open. Debug and Serde remain
excluded; TreeHash remains deferred.
