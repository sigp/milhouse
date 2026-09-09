# SSZ offset and encoder-construction source comparisons

This suite compares the local offset-decoding and encoder-construction models
with freshly extracted `ethereum_ssz` 0.10.0 code. Run from the repository root:

```sh
python3 scripts/aeneas-audit-ssz-offset-models.py
```

The fixture pins the dependency and its lockfile, aligned with the repository's
dependency versions. The shared runner pins Charon 0.1.223, Aeneas `b59d5188`,
and `nightly-2026-06-01` (Rust commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). It checks formatting, runs eight
native tests, validates dependency/source provenance, generates fresh Lean,
and compiles it with the four comparisons. The decoder comparisons use only
`propext`, `Classical.choice`, and `Quot.sound`; construction uses only `propext`.

| Comparison | Source and coverage |
| --- | --- |
| `width_agrees` | Actual `BYTES_PER_LENGTH_OFFSET` initializer, `src/lib.rs:57`, equals the local four-byte constant. |
| `decode_offset_agrees` | Actual private decoder, `src/decode.rs:364`, agrees for every slice. Exactly four bytes decode through `u32::from_le_bytes`; every other length returns the original `InvalidLengthPrefix { len, expected: 4 }`. |
| `read_offset_composition_agrees` | Source-level composition of the public `read_offset`, `src/decode.rs:353`: foundation prefix slicing followed by the extracted private decoder. Inputs shorter than four bytes preserve the original length error; longer inputs ignore their suffix. Direct extraction of this public body remains unavailable. |
| `container_agrees` | Actual `SszEncoder::container`, `src/encode.rs:95`, equals the local constructor for every buffer and fixed-byte count, including the returned buffer-release continuation. Retains the existing local `Vec::reserve` model explicitly. |

The decoder proof unfolds the actual `clone_from_slice` specialization loop,
including all four copies, checked increments, and the final termination test.
It needs no length, successful-copy, termination, or extra word-bound premise.
The separately named source error type is mapped constructor by constructor,
preserving all twelve variants and their payloads. Existing Aeneas byte,
array, slice/index, scalar, clone, and default foundations remain boundaries;
this is not an independent proof of their raw-memory implementations.

The native tests check short lengths 0–3 with exact error fields, all 32 single
bits plus zero and `u32::MAX`, three mixed-byte patterns with four suffix
lengths each, and the debug-profile rejection of two oversized offsets on
64-bit targets. Four additional tests check constructor prefix/capacity and
replacement-buffer release; offset accumulation and payload movement; repeated
finalization with cleared variable bytes and output replacement; callback-panic
write order; and reservation overflow before state creation. These native
checks supplement the source comparisons. Append/finalize source fidelity,
release-profile offset behavior, allocation failures, and Rust unwind-state
refinement are not proved by this suite.

## Constructor comparison and retained reservation model

The constructor source reserves space, stores the requested fixed-byte offset,
retains the returned buffer, and starts with empty variable bytes. The proof
compares the actual extracted structure field by field with the local encoder
and checks its returned continuation on every replacement encoder state. It
preserves every result of the retained reservation primitive, including failure
and divergence, without a caller-supplied bound or success premise.

The pinned Aeneas library has no builtin `Vec::reserve`. The generated external
template requests exactly `alloc.vec.Vec.reserve`, with the signature supplied
by the existing definition in `Tree.Ssz.Models`. The runner validates that
dependency's `alloc` provenance at `vec/mod.rs:1470`, its opaque declaration,
and the exact template name/signature. It **never compiles the axiom template**.
Instead, `SszSource/FunsExternal.lean` contains only:

```lean
import Tree.Ssz.Models
```

No new primitive or source-method body is defined. The imported module must
already be an explicit build target and hashed model input. The generated
constructor is unchanged; its comparison uses only `propext`. The report
records the retained local primitive under `retainedLocalFoundations`.

This establishes the constructor relative to the existing reservation model.
It does not independently verify Rust allocation, capacity, or reservation
failures. That model retains logical word-size overflow while abstracting
allocation behavior, as documented in `PROGRESSIVE_LIST_MODEL_AUDIT.md`.
Other suites continue to reject all external templates unless they explicitly
declare and validate such an existing foundation binding.

## Retaining and naming the actual dependency declarations

Charon can select the private `ssz::decode::decode_offset` as an external root.
Aeneas's unused-function pass nevertheless drops nonlocal functions without
retained callers (`PrePasses.ml:2145`). Changing Rust visibility
metadata alone does not retain it. The runner validates the original
transparent dependency body and then changes only its `is_local` metadata to
retain it as an extraction root.

The generated source `DecodeError` also needs a distinct name: importing it
alongside `Tree.Types` otherwise collides on the generated global instance
`instDiscriminantDecodeErrorIsize`, despite the separate module namespace.
The runner verifies the transparent source enum's crate and file, then changes
only its final name identifier to `SourceDecodeError`.

`check_source_metadata` reverses both adjustments in a copy and requires
equality with the **entire original LLBC**. Code, signatures, function/type IDs,
call targets, fields, discriminants, dictionaries, spans, and every other
field must be unchanged. The original input is saved as
`original-metadata.llbc`. Missing adjustments, duplicate declarations,
collisions, extra mutations, or invalid source provenance fail the audit.
No Rust code or generated Lean body is patched, and Aeneas source is unchanged.

## Remaining direct extraction limitations

The actual encoder's append and finalization bodies fail on borrowing the
stored mutable output buffer. The callers are preserved in `source.rs`.
From the repository root:

```sh
ssz_state_audit_dir=$(mktemp -d /tmp/milhouse-ssz-state-XXXXXX)
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include ssz::encode::SszEncoder --include 'ssz::encode::_::container' \
  --include 'ssz::encode::_::finalize' --start-from ssz_source::container \
  --start-from ssz_source::finalize --dest-file "$ssz_state_audit_dir/ssz_source.llbc" \
  -- --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/ssz_offset_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace SszEncoderSource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$ssz_state_audit_dir/State" "$ssz_state_audit_dir/ssz_source.llbc"
```

Charon succeeds; Aeneas exits 1. `finalize` reports `Can't copy a mutable
borrow` at `encode.rs:130` (`InterpExpressions.ml:197`, then `Interp.ml:609`).
The caller also reports `Could not find var for symbolic value: 10`
(`SymbolicToPureCore.ml:520`). Selecting append separately:

```sh
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include ssz::encode::SszEncoder --include 'ssz::encode::_::container' \
  --include 'ssz::encode::_::finalize' --include 'ssz::encode::_::append' \
  --include 'ssz::encode::_::append_parameterized' --include ssz::encode::Encode \
  --include ssz::encode::encode_length --include ssz::BYTES_PER_LENGTH_OFFSET \
  --include ssz::MAX_LENGTH_VALUE --start-from ssz_source::append \
  --dest-file "$ssz_state_audit_dir/append.llbc" -- --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/ssz_offset_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace SszEncoderSource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$ssz_state_audit_dir/Append" "$ssz_state_audit_dir/append.llbc"
```

Again Charon succeeds and Aeneas exits 1: `append_parameterized` reports
`Can't copy a mutable borrow` at `encode.rs:116`, from the same interpreter
locations. The successful audit selects only the constructor and decoder
roots, and imports no partial append/finalize body. No Aeneas or dependency
Rust source is changed.

The public borrowed reader still fails even when its Option operations and
the private decoder's copy loop are included. Reproduce from the repository
root:

```sh
ssz_read_audit_dir=$(mktemp -d /tmp/milhouse-ssz-read-XXXXXX)
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include ssz::decode::read_offset --include ssz::decode::decode_offset \
  --include ssz::decode::DecodeError --include ssz::BYTES_PER_LENGTH_OFFSET \
  --include core::option --include 'core::slice::_::clone_from_slice' \
  --include 'core::slice::_::spec_clone_from' \
  --start-from ssz_source::read_offset \
  --dest-file "$ssz_read_audit_dir/ssz_source.llbc" -- --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/ssz_offset_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace SszSource -split-files \
  -no-progress-bar -print-error-emitters -print-error-diagnostics \
  -dest "$ssz_read_audit_dir/SszSource" "$ssz_read_audit_dir/ssz_source.llbc"
```

Charon succeeds; Aeneas exits 1 with `There should be no bottoms in the value`
at `decode.rs:360` (`InterpExpressions.ml:55`, then `Interp.ml:609`). The
composition comparison above makes this remaining boundary explicit and
imports no failed/partial output.

The encoder has a separate foundation limitation:

```sh
ssz_encode_audit_dir=$(mktemp -d /tmp/milhouse-ssz-encode-XXXXXX)
../aeneas/charon/bin/charon cargo --preset=aeneas \
  --include ssz::encode::encode_length --include ssz::BYTES_PER_LENGTH_OFFSET \
  --include ssz::MAX_LENGTH_VALUE --start-from ssz_source::encode_length \
  --dest-file "$ssz_encode_audit_dir/ssz_source.llbc" -- --offline --locked \
  --manifest-path "$PWD/aeneas-lean/reproducers/ssz_offset_models/Cargo.toml"
../aeneas/bin/aeneas -backend lean -namespace SszSource -split-files \
  -no-progress-bar -dest "$ssz_encode_audit_dir/SszSource" \
  "$ssz_encode_audit_dir/ssz_source.llbc"
ssz_lean=$(cd aeneas-lean && lake env which lean)
ssz_lean_path=$(cd aeneas-lean && lake env printenv LEAN_PATH)
(
  cd "$ssz_encode_audit_dir"
  export LEAN_PATH="$ssz_encode_audit_dir:$ssz_lean_path"
  "$ssz_lean" -o SszSource/Types.olean SszSource/Types.lean
  "$ssz_lean" -o SszSource/Funs.olean SszSource/Funs.lean
)
```

Charon and Aeneas succeed, but the generated function fails Lean elaboration:
`Unknown identifier core.num.Usize.to_le_bytes` (`Funs.lean:47`). The builtin
mapping names that operation, while the pinned foundation byte-conversion
definitions use `uscalar_no_usize`. No assumed replacement is added. These
findings concern extraction/foundation support and establish no Rust bug.

## Audit record and limits

Successful runs write `.lake/ssz-offset-model-audit/report.json` with tool pins,
dependency and input hashes, original source spans, metadata adjustments, and
exact axiom dependencies. Any previous report is removed before a new run.
Validation rejected nine malformed source inventories, eighteen invalid
metadata/provenance/configuration cases, and four invalid axiom reports.
The constructor extension also rejects seven malformed templates, seven
invalid foundation source inventories, four invalid binding configurations,
and four invalid axiom reports. All six other source suites pass with this
runner extension. The suite has three direct comparisons and one composition
check. Append/finalize, reservation fidelity, other SSZ/model boundaries,
borrowed CoW, and the remaining assumption review stay open. The main library proofs and model-root inventory
are unchanged. Debug and Serde remain excluded; TreeHash remains deferred.
