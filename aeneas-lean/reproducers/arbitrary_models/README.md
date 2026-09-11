# Arbitrary model source comparisons

The September 7 migration retains all 3 proofs in this suite. Use the
[project toolchain setup](../../README.md) and the pinned defaults of its
audit command. Earlier compiler pins, source locations, and checkpoint
counts below are historical; current versions and input hashes are recorded
in each new audit report. The temporary `usize::pow` assumption does not
exclude any proof in this suite.

Run from the repository root:

```sh
python3 scripts/aeneas-audit-arbitrary-models.py
```

The suite compares both size-hint defaults and `milhouse.arbitrary.nextControl`
with pinned `arbitrary` 1.4.1 source. The control comparison uses the actual
`bool::arbitrary` implementation. It includes
the actual `u8::arbitrary` and `Unstructured::fill_buffer` bodies, including
the zero-fill iterator loop. No generator implementation is substituted.

The shared runner pins Charon 0.1.223, Aeneas `b59d5188`, and
`nightly-2026-06-01` (Rust commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). It checks formatting, runs eight
native tests, validates original dependency provenance, generates complete
Lean files, and compiles them with `CheckModels.lean`. The control and fixed
hint comparisons use only `propext`, `Classical.choice`, and `Quot.sound`;
the fallible hint comparison uses only `propext`.

## Proved behavior

`size_hint_default_agrees` compares the actual trait default at `src/lib.rs:320`
with the local model: it ignores every callback and depth and returns
`(0, None)`. `try_size_hint_default_agrees` compares the default at
`src/lib.rs:423`: it calls the dictionary's actual `size_hint`, wraps a
successful answer in `Ok`, and preserves failure or divergence. Neither
comparison requires callback consistency, termination, or a depth bound.

The proof adapts the complete dictionary through the input/error representation
mapping. All four callbacks are retained; none is replaced by a constant.
Both comparison equalities follow by reflexivity with only the listed standard
axioms.

The control comparison covers every input slice and both outputs: the Boolean result
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

The control function's provenance filter selects `arbitrary::foreign::core::bool`, so
the identically named byte-generator method cannot be mistaken for the bool
method being compared. Type provenance is checked separately against the
dependency crate. The generated `Error` discriminant instance otherwise
collides with `Tree.Types` as `instDiscriminantErrorIsize`. The source type's
final metadata name becomes `SourceError`. Along with the trait labels below,
these are the only changes allowed to the selected LLBC. Restoring them must
recover the **entire original selected LLBC**. Source bodies, signatures,
fields, IDs, calls, dictionaries, and spans must remain unchanged.
The original input is preserved as `original-metadata.llbc`.

## Trait names and the unused owning default

The generic source trait's first field is named `arbitrary`. That name shadows
the dependency namespace in subsequent generated field types. The audit changes
only this trait method's two name labels to `generate_source`: its field name
and final metadata identifier. Original transparent trait/method provenance,
method position/ID, and fresh-name uniqueness are checked. Restoring those two
labels and the error type name must recover the entire original selected LLBC. Signatures,
callback IDs, defaults, calls, and trait dictionaries remain unchanged. No
generated Lean body or Aeneas source is patched.

Direct extraction still fails on the unused owning-input default. Each audit
first extracts unfiltered expanded LLBC, then excludes exactly
`arbitrary::Arbitrary::arbitrary_take_rest`. It compares all three complete
source declarations before and after the exclusion. Charon assigns fresh
statement IDs using a global counter, so removing an earlier body renumbers
the later statements. Its own `Statement` equality ignores these IDs
(`ast/llbc_ast.rs:126`, `ast/llbc_ast_utils.rs:61`).

The runner checks a one-to-one correspondence of nonnegative integer IDs
within each compared body, restores them only in the comparison copy, and
records each change. The pinned four-field Statement schema is required;
every other field of every source declaration must remain equal. The current
run renumbers seven statements in `size_hint` and twelve in `try_size_hint`.
Code, source spans, function/type/callback IDs, and control flow cannot change.
The compiled input retains Charon's selected IDs unchanged. This exception is
enabled only for this suite; existing exclusion checks remain strict.

## Native coverage and remaining source boundaries

The eight tests cover all 256 control-byte values and repeated exhaustion;
768 one-byte buffer overwrites; even stopping-byte consumption; exact input
after the first element error; generator input replacement that produces two
elements from a one-byte initial input; panic short-circuiting; the owning
trait default's ordinary-generator dispatch; and both size-hint defaults,
including a custom hint, maximum depth, and exact hint-callback panic dispatch.
These checks supplement the three source comparisons. Full vector generation
and the owning-input trait default remain source boundaries.

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
by `Interp.ml:609`). This unfiltered output is not imported. The successful
audit uses the checked exclusion and name adjustments described above.

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
The size-hint extension rejected nine malformed source inventories, fifteen
invalid trait/metadata/configuration cases, nine invalid exclusion/statement
cases, and four invalid axiom reports. Earlier control-only validation also
rejected ten malformed inventories and ten metadata/type-namespace cases.
All six existing source-comparison suites also pass with the shared runner change. The main
proof library and model-root inventory are unchanged; their gates were not
repeated for this standalone audit. Remaining Arbitrary/model boundaries,
borrowed CoW, and the assumption review stay open. Debug and Serde remain
excluded; TreeHash remains deferred.
