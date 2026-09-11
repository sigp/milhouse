# ProgressiveList CoW proof status

The goal remains in progress. Acquisition and consuming mutation have
high-level correctness results; borrowed handle access and iterator stepping
still need extraction and proofs. These obligations are not replaced by
observations of handle data or by the consuming-method theorems.

## Rust bug found during write-back composition

The subsequent review confirmed that nested `MaxMap<MaxMap<M>>` loses the
inner handle's maximum callback. CoW insertion at key 17 leaves an original
inner maximum of 3 unchanged even though the inner map now contains key 17.
The outer maximum and lookups remain correct in the reproducer. All eight
combinations of VecMap/BTreeMap, supplied/lazy acquisition, and consuming/
borrowed mutation fail the inner-cache assertion; the read-only and direct
mutation control passes. See the [native reproducer](reproducers/nested_max_map_cow/README.md).

This is a Rust callback-composition bug, independent of the Aeneas extraction
failures. `releaseIndex` restores the original inner callback unchanged,
whereas the inner `Written` contract requires recording it. The existing
outer-maximum and conditional list theorems remain valid. No premise was
added to conceal this mismatch. Proof changes stopped and the bug was raised
as required by `AGENTS.md`; the goal remains incomplete.

## Verified source composition

The September 11 continuation adds 22 named lemmas in five modules:

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

The complete consuming theorem retains represented input, an in-bounds key,
the selected acquisition read law, structural entry readiness and actual
immutable-clone termination, and selected write-back read agreement. The
clone result may differ from the original value. It assumes neither an
intermediate CoW success nor an independent maximum law, packing invariant,
or backing-shape invariant. The source wrapper transfers several inner laws;
it does not establish arbitrary inner-map behavior from Rust trait bounds.

Error restoration needs only the selected unchanged-release law and the
actual acquisition/error results. It requires no representation, index bound,
read, clone, entry-readiness, or maximum law. This concerns returned Rust
`Err` values, not panic recovery or divergence.

## Open obligations

- Prove the actual Rust `Deref` and borrowed `Cow::make_mut` methods. Handle
  value observation and `Cow::into_mut` do not establish either method.
- Extract and prove `ProgressiveListIterCow::next_cow`, including traversal,
  mutation, metadata, and termination behavior. Constructor proofs alone
  do not establish stepping.
- Complete concrete inner-map/entry fidelity and the remaining selected
  read-back contracts. The independent VecMap source suite covers observers
  and mutable lookup; insertion and its iterator dependencies remain outside
  the successful source suite.

Current production probes of `make_mut` and `next_cow` use the adopted
Aeneas `7ebd01d` / Charon `85bba1f2` / Rust `nightly-2026-08-18` with full MIR.
Charon reports no LLBC errors; Aeneas exits 1 on both added roots. `make_mut`
still loses borrowed symbolic values and fails backward projection.
`next_cow` still fails on its borrowed fallback closure and missing symbolic
values. Logs and source hashes are in `.lake/cow-goal-probes/`.
No partial output is imported into the proof library.

Selecting the `Cow` Deref trait method alone exited zero but emitted none of
the required Cow/BTreeCow/VecCow Deref bodies, so this was not successful
coverage. A concrete caller in an isolated worktree forced the actual
methods into extraction:

```rust
pub fn cow_deref_probe<'a, 'b, T: Clone>(handle: &'b crate::Cow<'a, T>) -> &'b T {
    std::ops::Deref::deref(handle)
}
```

Charon succeeded without LLBC errors; Aeneas exited 1 on both inner Deref
methods with `Unreachable`. The caller patch, full-MIR LLBC, and failure log
are retained as `deref-caller.*` in the same diagnostic directory. The caller
and partial generated output were not added to production.

## Validation

The complete Lean build passes (2,176 jobs). The axiom/import audit covers
6,251 theorem declarations, including private/generated declarations, across
454 modules. All added lemmas use only standard Lean axioms; the same 119
declarations retain the existing Arc pointer contract. The model audit still
covers 42 roots and 151 local model declarations. Production Rust, generated
Rust extraction, and external models are unchanged by this proof work.
The approved `usize::pow` source assumption is unchanged. Debug and Serde
remain out of scope, and TreeHash remains deferred.
