# ProgressiveList CoW proof status

Completion of the CoW goal is blocked on the pinned compiler's translation of
borrowed handle access and iterator stepping. Acquisition and consuming
mutation have high-level correctness results. The missing method obligations
are not replaced by observations of handle data or by the consuming-method
theorems. No supported workaround for the actual borrowed methods has been
established by the probes below. Aeneas source changes remain outside the
repository's instructions; no additional source assumptions are introduced.

## Callback composition repaired

Commit `c7e5128` fixes the nested `MaxMap<MaxMap<M>>` callback bug. The first
maximum callback stays inline; attaching an additional wrapper links the
previous callback in a box. Running the chain records every original maximum
and clears every action. Read-only release restores all original borrows.
The common single-wrapper path allocates no callback node; nested wrappers
allocate one node per additional callback.

All 333 Rust library tests pass, including the eight nested-map cases that
previously failed and their read-only/direct-mutation control. The
[original native reproducer](reproducers/nested_max_map_cow/README.md) remains
available against the historical baseline. The new source extracts with full
MIR and introduces no external models. A guarded postprocessor supplies a
type annotation for one generated empty-chain continuation; it changes no
expression behavior and no Aeneas source.

`CowOnMut.run_eq` now proves complete chain recording. The new
[CallbackAttachment.lean](Tree/Cow/CallbackAttachment.lean) proves exact
attachment/release and preservation of all recorded inner callbacks.
`Cow.releaseIndex_written` establishes the original inner handle's complete
`Written` footprint, without a callback-neutrality or metadata premise.

Commit `b1842b8` uses that result in
[MaxMap/CowWriteBack.lean](Tree/UpdateMap/MaxMap/CowWriteBack.lean) to transfer
both exact insertion/read framing and selected fallback-aware write agreement.
It also transfers precise entry readiness and immutable-clone termination.
[CopyOnWrite/MaxMapInner.lean](Tree/ProgressiveList/CopyOnWrite/MaxMapInner.lean)
provides the high-level represented-replacement and complete consuming-mutation
contracts using only the selected **inner-map** read, materialization-input,
and write-read laws. The wrapper's callback and maximum behavior is derived
from source. This removes the callback-composition obstacle without narrowing
the supported nested-map configurations.

## Verified source composition

The initial September 11 continuation added 22 named lemmas in five modules:

| Module | Established behavior |
| --- | --- |
| [Cow/Attachment.lean](Tree/Cow/Attachment.lean) | Exact source attachment and continuation; preservation of carried value, entry location, clone requirement, and unchanged release; every filled footprint records the outer key |
| [UpdateMap/MaxMap/CopyOnWrite.lean](Tree/UpdateMap/MaxMap/CopyOnWrite.lean) | Exact supplied-value acquisition and continuation; transfers of the inner read, unchanged-release, entry-location, and existing-mutable contracts; unconditional insertion-maximum law for filled footprints |
| [ProgressiveList/CopyOnWrite/MaxMap.lean](Tree/ProgressiveList/CopyOnWrite/MaxMap.lean) | In-bounds length preservation, represented-element replacement, and acquisition followed by consuming mutation through the actual MaxMap dictionary, without an independent maximum-index law |
| [Cow/Errors.lean](Tree/Cow/Errors.lean) | Every actual Rust-level consuming error is `CowMissingEntry` and returns the original handle through every continuation input |
| [ProgressiveList/CopyOnWrite/Errors.lean](Tree/ProgressiveList/CopyOnWrite/Errors.lean) | Consuming-error restoration of the complete list under only selected unchanged release; MaxMap specialization requires only the inner release law |

The commits are `50f5250`, `61e4b11`, `910a745`, `b05aedc`, and `28465ee`.
All existing generic theorems remain available. The new helper definitions
characterize the actual extracted functions by proved equations; they do not
replace Rust implementations or add external models.

## Remaining assumptions

The MaxMap maximum law is derived from its actual attached callback, with
no inner maximum-query contract, cache-validity invariant, index bound, or
clone law. An in-bounds key is needed when using that law to preserve list
length; the representation hypothesis supplies the successful original
length. Out-of-bounds insertion could increase the logical extent.

The newest complete consuming theorem retains represented input, an in-bounds
key, and the selected inner-map acquisition read law, structural entry
readiness and actual immutable-clone termination, and write-back read
agreement. The clone result may differ from the original value. It assumes neither an
intermediate CoW success nor an independent maximum law, packing invariant,
or backing-shape invariant. The source wrapper transfers several inner laws;
it does not establish arbitrary inner-map behavior from Rust trait bounds.

Error restoration needs only the selected unchanged-release law and the
actual acquisition/error results. It requires no representation, index bound,
read, clone, entry-readiness, or maximum law. This concerns returned Rust
`Err` values, not panic recovery or divergence.

## Concrete VecMap entry progress

Commit `1a93d59` extends the independent
[VecMap source suite](reproducers/vec_map_models/README.md) to 16 proofs and
five native tests. The new contracts establish actual `contains_key` and
`entry` execution, including occupancy classification, retention of the exact
map and key, and the full release continuation. Entry acquisition and unchanged
release need no count, clone, allocation, or key-bound premise. The returned
entry uses the actual source map representation, not an assumed slot model.

This separates entry acquisition from another extraction failure:
`OccupiedEntry::into_mut` is rejected with `Can't copy a mutable borrow` at
`vec_map`'s `&mut self.map[index]`. Charon succeeds with error-free full-MIR
LLBC, but Aeneas exits 1. The partial body is not imported. This obstacle is
independent of the already documented insertion iterator failures. The
concrete CoW adapter and complete entry-footprint refinement remain open.

## Open obligations

- Prove the actual Rust `Deref` and borrowed `Cow::make_mut` methods. Handle
  value observation and `Cow::into_mut` do not establish either method.
- Extract and prove `ProgressiveListIterCow::next_cow`, including traversal,
  mutation, metadata, and termination behavior. Constructor proofs alone
  do not establish stepping.
- Complete concrete inner-map/entry fidelity and the remaining selected
  read-back contracts. The independent VecMap source suite covers observers
  and mutable lookup as well as entry acquisition; vacant insertion and
  occupied-entry consumption remain outside the successful source suite.

Fresh probes after the callback repair use the adopted
Aeneas `7ebd01d` / Charon `85bba1f2` / Rust `nightly-2026-08-18` with full MIR.
Charon reports no LLBC errors; Aeneas exits 1 on `make_mut`, `next_cow`,
and a concrete `Deref` caller. `make_mut` still loses borrowed symbolic values and fails backward projection.
`next_cow` still fails on its borrowed fallback closure and missing symbolic
values. Current logs, source hashes, and exact extraction checks are in
`.lake/cow-callback-chain-probe/`.
No partial output is imported into the proof library.

The earlier selection of the `Cow` Deref trait method alone exited zero but
emitted none of the required Cow/BTreeCow/VecCow Deref bodies, so this was not successful
coverage. A concrete caller in an isolated worktree forced the actual
methods into extraction:

```rust
pub fn cow_deref_probe<'a, 'b, T: Clone>(handle: &'b crate::Cow<'a, T>) -> &'b T {
    std::ops::Deref::deref(handle)
}
```

Charon succeeded without LLBC errors; Aeneas exited 1 on both inner Deref
methods with `Unreachable`. The original caller patch and logs remain in
`.lake/cow-goal-probes/`; the repaired source has the same failure, recorded
under `.lake/cow-callback-chain-probe/deref-caller/`. The caller and partial
generated output are not imported into production.

An additional focused run at `521171d` enables `-checks` on this same concrete
Deref caller. Charon produces error-free full-MIR LLBC; Aeneas exits 1 with
`Could not find borrow b@2` in both inner methods and an invariant failure in
the outer method. The exact caller patch, LLBC hash, and diagnostics are under
`.lake/cow-blocked-audit/`. The tested variants do not establish that every
possible Rust rewrite would fail, but they provide no extractable body for the
required proof. The remaining concrete VecMap operations have the separate
insertion and occupied-entry failures described above.

## Validation

The complete Lean build passes (2,180 jobs). The axiom/import audit covers
6,309 theorem declarations, including private/generated declarations, across
458 modules. All added proofs use only standard Lean axioms; the same 119
declarations retain the existing Arc pointer contract. The model audit still
covers 42 roots and 151 local model declarations. Fresh full-MIR extraction
reproduces all four generated production files exactly and preserves the
lockfile. All 333 Rust library tests and 17 Python checker tests pass.

The SSZ-offset and Arbitrary source suites were refreshed for the changed
`Tree/Types.lean` input; both pass. All eight source reports are current. The subsequent VecMap
entry extension increases their total to 54 proofs. Callback-repair logs and hashes are
under `.lake/cow-callback-chain-probe/`, and the entry/occupied diagnostics
are under `.lake/cow-concrete-map-probe/`. The approved `usize::pow` source
assumption and external models are unchanged. Debug and Serde remain out of
scope, and TreeHash remains deferred. Borrowed methods and the remaining
concrete inner-map/entry fidelity still prevent completion of the goal.

The subsequent compiler-cleanup commit `d453198` restores ordinary loops in
SSZ encoding and slow list removal. It leaves CoW implementations and all
semantic proof premises unchanged. The complete 2,180-job build and axiom
audit still pass with 6,309 declarations across 458 modules and identical
axiom dependencies. The model audit and all 333 Rust tests pass. The SSZ-offset
and Arbitrary source reports were refreshed for shifted source annotations;
all eight reports have current inputs and retain 54 proofs. Evidence is under
`.lake/sept7-remaining-loops/`.
