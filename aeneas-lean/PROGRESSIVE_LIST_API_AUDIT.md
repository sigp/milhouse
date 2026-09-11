# ProgressiveList source and proof inventory

Current compiler migration: September 7 Aeneas, with the user-approved
2026-09-11 exception that `usize::pow` source correspondence is assumed.
Its concrete Lean model and all dependent operation proofs remain in place.
The required source suites contain 51 proofs; the old power comparison is
deferred. Earlier nine-suite/52-proof counts below are historical.
See [the assumption policy](SOURCE_MODEL_ASSUMPTIONS.json) and
[compiler migration status](SEPT7_TRIAL_STATUS.md). Public API coverage and
the Debug/Serde exclusions and TreeHash deferral are unchanged.

Source checkpoint: `0ed21ba`. This inventory names the Rust entry points and
their current proof entry points, unresolved obligations, or scope exclusions.
It complements the [coverage and validation record](PROGRESSIVE_LIST_PROOFS.md);
it is not a claim of complete correctness, model fidelity, or minimal theorem
hypotheses.

The SSZ reflection and success-criterion proof checkpoint is `029fdc4`.
The subsequent empty-input premise audit is through `b41b66a`.
The constructor trace and complete success-criterion checkpoint is `ed766a4`.
The local model dependency audit is through `07ef38d`; its
[separate report and gate](PROGRESSIVE_LIST_MODEL_AUDIT.md) cover the 42
available included extraction roots without counting unavailable borrowed
methods or excluded/deferred implementations.
The subsequent tuple-model correction and branch proofs are through `c47faba`;
both full-library audit gates pass after that correction.
The borrowed-read diagnostic checkpoint `56924d0` adds a standalone reproducer
and verified controls, with no additional public-operation proof coverage.
The packing-layout premise audit is through `0932572`: both layout constructors
drop the redundant packing-depth query argument, derived by `69d2ec6` from
the factor query and power law. All dependent operation proofs build.

Scope revision (2026-09-09): **Debug implementations and Serde implementations
are out of scope**, including both iterator Debug derives, in-place
deserialization, and Serde-based context deserialization with its visitor/seed
protocols. Excluded rows are retained for source accounting and do not count
as unfinished goal obligations. The subsequent scope revision also defers
TreeHash implementations for now, including root hashing and shared-cache
writes. Existing metadata and packing-rejection proofs are retained. SSZ
encoding/decoding and cache assumptions needed by rebasing remain in scope. See
the [revised goal](PROGRESSIVE_LIST_PROOFS.md#goal-and-scope).

The source search covered `src/progressive_list.rs`, other production uses of
`ProgressiveList`, `src/cow.rs`, `src/serde.rs`, `src/context_deserialize.rs`,
the extraction script, and the concrete trait callers in `src/proof_roots.rs`.
All 19 public inherent methods in `src/progressive_list.rs` are accounted for
below. The iterator types are defined in that same file.

## Inherent list methods

Proof names below are in `milhouse.progressive_list`. Their full hypotheses
and auxiliary state/error/cache results are described in the coverage record.

| Rust method | Primary proof entry point |
| --- | --- |
| `empty` | `ProgressiveList.empty_represents`, `ProgressiveList.empty_spec` |
| `new` | `ProgressiveList.new_total_spec_of_overlay`, `ProgressiveList.new_success_represents_iff`, `ProgressiveList.new_represents_iff`, `ProgressiveList.new_success_iff` |
| `try_from_iter` | `ProgressiveList.try_from_iter_total_spec_of_overlay`, `ProgressiveList.try_from_iter_success_represents_iff`, `ProgressiveList.try_from_iter_represents_iff`, `ProgressiveList.try_from_iter_trace`, `ProgressiveList.try_from_iter_success_iff` |
| `get` | `ProgressiveList.get_of_pending_update`, `ProgressiveList.get_of_backing`, `ProgressiveList.represents_of_dense_backing`; constructors and mutations establish/preserve indexed representation |
| `get_mut` | `ProgressiveList.get_mut_total_spec_of_fallback` (laws only for the actual fallback), `ProgressiveList.get_mut_value_success_iff_of_fallback`, `ProgressiveList.get_mut_success_iff_inputs_of_fallback`, `ProgressiveList.get_mut_present_success_iff_clone_of_fallback`; `ProgressiveList.get_mut_represents_set_iff` retains the exact write-back criterion |
| `get_cow` | `ProgressiveList.get_cow_represents_read_of_fallback`, `ProgressiveList.get_cow_into_mut_spec_of_materialization`, `ProgressiveList.get_cow_into_mut_success_iff_of_fallback`, `ProgressiveList.cow_writeback_represents_set_iff`; `get_cow_read_eq_get_iff_fallback` and `get_cow_read_only_preserves_self_iff_fallback` establish exact read/release law requirements. Original stronger signatures remain adapters; borrowed handle methods remain pending below |
| `push` | `ProgressiveList.push_total_spec`, `ProgressiveList.push_represents_append_iff`, `ProgressiveList.len_after_push_iff_max_index`, `ProgressiveList.push_represents_append_iff_max_index` |
| `len` | `ProgressiveList.len_total_spec`, `ProgressiveList.len_success_iff` |
| `is_empty` | `ProgressiveList.is_empty_total_spec`, `ProgressiveList.is_empty_true_iff` |
| `has_pending_updates` | `ProgressiveList.has_pending_updates_spec` |
| `apply_updates` | `ProgressiveList.apply_updates_success_valid_materializes_iff_of_inputs`, `ProgressiveList.apply_updates_success_valid_materializes_represents_iff_of_inputs`, `ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_selected_clones_skipped` (only layout and input representation/backing preconditions; clone/range conditions in the exact criterion); `ProgressiveList.apply_updates_total_spec_of_guards`, `ProgressiveList.apply_updates_success_valid_materializes_iff_of_binary_selection`, `ProgressiveList.apply_updates_success_valid_materializes_represents_iff_of_binary_selection`, `ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_clones_skipped` (no range-value reflection; numeric binary selection remains); `ProgressiveList.apply_updates_preserves_backing_of_all_range_extents`, `ProgressiveList.apply_updates_preserves_backing_of_skipped_ranges` (backing preservation without range-value reflection); `ProgressiveList.apply_updates_nonempty_success_of_guards`, `ProgressiveList.apply_updates_nonempty_success_iff_guards`, `ProgressiveList.apply_updates_success_iff_guards` (execution without range correctness); `ProgressiveList.apply_updates_total_spec_of_enabled`, `ProgressiveList.apply_updates_success_valid_materializes_iff_of_ranges`, `ProgressiveList.apply_updates_success_valid_materializes_represents_iff_of_ranges`, `ProgressiveList.apply_updates_total_spec_of_skipped`, `ProgressiveList.apply_updates_success_represents_iff_of_skipped`, `ProgressiveList.apply_updates_represents_iff_of_range_extents`, `ProgressiveList.apply_updates_nonempty_backing_reads_iff_layer_agreement`, `ProgressiveList.apply_updates_backing_valid_contents_iff`, `ProgressiveList.apply_updates_nonempty_backing_contents_iff_layer_agreement`, `ProgressiveList.apply_updates_success_materializes_iff`, `ProgressiveList.apply_updates_success_materializes_represents_iff`, `ProgressiveList.len_after_apply_updates_iff` |
| `iter` | `ProgressiveList.iter_spec` |
| `iter_from` | `ProgressiveList.iter_from_spec`, `ProgressiveList.iter_from_error_iff` |
| `iter_cow` | `ProgressiveList.iter_cow_spec`; constructor only, stepping pending |
| `iter_cow_from` | `ProgressiveList.iter_cow_from_spec`, `ProgressiveList.iter_cow_from_error_iff`; stepping pending |
| `to_vec` | `ProgressiveList.to_vec_total_spec`, `ProgressiveList.to_vec_mapM` |
| `pop_front` | `ProgressiveList.pop_front_nonzero_overlay_total_spec`, `ProgressiveList.pop_front_success_represents_iff`, `ProgressiveList.pop_front_nonzero_represents_iff`, `ProgressiveList.pop_front_total_spec`, `ProgressiveList.pop_front_success_iff`, `ProgressiveList.pop_front_out_of_bounds` |
| `rebase` | `ProgressiveList.rebase_total_spec_of_inputs`, `ProgressiveList.rebase_success_represents_iff`, `ProgressiveList.rebase_represents_iff`, `ProgressiveList.rebase_reads_eq_iff`, `ProgressiveList.rebase_cache_iff_of_inputs` |
| `rebase_on` | `ProgressiveList.rebase_on_total_spec_of_inputs`, `ProgressiveList.rebase_on_success_represents_iff`, `ProgressiveList.rebase_on_represents_iff`, `ProgressiveList.rebase_on_get_eq`, `ProgressiveList.rebase_on_cache_iff_of_inputs` |

## List trait methods

The pinned dependency sources were checked for additional methods:
`ethereum_ssz` 0.10.0 (`Encode`: five, `Decode`: three), `tree_hash` 0.12.0
(four), `serde` 1.0.217 (`Serialize`: one, `Deserialize`: two), `arbitrary`
1.4.1 (four), and `context_deserialize` 0.2.0 (one). In particular, the context
trait has no additional in-place default. Ordinary Serde does.

| Trait method | Primary proof entry point, remaining obligation, or scope exclusion |
| --- | --- |
| `Default::default` | `ProgressiveList.default_eq_empty`, `ProgressiveList.default_represents` |
| `TryFrom<Vec<T>>::try_from` | `ProgressiveList.try_from_vec_total_spec_of_overlay`, `ProgressiveList.try_from_vec_success_represents_iff`, `ProgressiveList.try_from_vec_represents_iff`, `ProgressiveList.try_from_vec_success_iff` |
| `TryFromIter::try_from_iter` | `ProgressiveList.ssz_try_from_iter_total_spec_of_overlay`, `ProgressiveList.ssz_try_from_iter_success_represents_iff`, `ProgressiveList.ssz_try_from_iter_represents_iff`, `ProgressiveList.ssz_try_from_iter_success_iff` |
| `IntoIterator::into_iter` for `&ProgressiveList` | `ProgressiveList.into_iter_spec` |
| `Clone::clone` | `ProgressiveList.clone_total_spec`, `ProgressiveList.clone_success_iff`, `ProgressiveList.clone_success_represents_iff` |
| `Clone::clone_from` | `ProgressiveList.clone_from_total_spec`, `ProgressiveList.clone_from_success_represents_iff`; actual inherited method, made reachable by a concrete caller |
| `PartialEq::eq` | `ProgressiveList.partial_eq_spec`, `ProgressiveList.partial_eq_represents` |
| `PartialEq::ne` | `ProgressiveList.partial_ne_spec`; actual trait default |
| `Debug::fmt` | Out of scope. Historical extraction/model findings: UPSTREAM_BUGS issue 5 |
| `TreeHash::tree_hash_type` | TreeHash deferred for now; retained proof: `ProgressiveList.tree_hash_type_eq` |
| `TreeHash::tree_hash_packed_encoding` | TreeHash deferred for now; retained proof: `ProgressiveList.tree_hash_packed_encoding_panics` |
| `TreeHash::tree_hash_packing_factor` | TreeHash deferred for now; retained proof: `ProgressiveList.tree_hash_packing_factor_panics` |
| `TreeHash::tree_hash_root` | Deferred and out of scope for now, including pending-update rejection, length mix-in, parallel calls, and shared-cache writes. Aeneas limitations: issue 21 |
| `Encode::is_ssz_fixed_len` | `ProgressiveList.ssz_is_fixed_len_eq` |
| `Encode::ssz_fixed_len` | `ProgressiveList.ssz_fixed_len_eq` |
| `Encode::ssz_bytes_len` | `ProgressiveList.ssz_bytes_len_fixed_total_spec` and `ProgressiveList.ssz_bytes_len_variable_spec` give exact sizes; `ProgressiveList.ssz_bytes_len_fixed_eq` and `ProgressiveList.ssz_bytes_len_variable_calls` retain actual calls and checked arithmetic, including failure/divergence |
| `Encode::ssz_append` | `ProgressiveList.ssz_append_fixed_calls` and `ProgressiveList.ssz_append_variable_calls` preserve actual ordered calls and failures without codec laws or byte/offset bounds; `ProgressiveList.ssz_append_fixed_spec` and `ProgressiveList.ssz_append_variable_spec` give exact bytes |
| `Encode::as_ssz_bytes` | `ProgressiveList.as_ssz_bytes_fixed_calls` and `ProgressiveList.as_ssz_bytes_variable_calls` give actual call behavior; `ProgressiveList.as_ssz_bytes_fixed_spec` and `ProgressiveList.as_ssz_bytes_variable_spec` give exact bytes |
| `Decode::is_ssz_fixed_len` | `ProgressiveList.decode_is_fixed_len_eq` |
| `Decode::ssz_fixed_len` | `ProgressiveList.decode_fixed_len_eq` |
| `Decode::from_ssz_bytes` | `ProgressiveList.from_ssz_bytes_represents_iff`, `ProgressiveList.from_ssz_bytes_success_represents_iff`, `ProgressiveList.from_ssz_bytes_trace_total_spec_of_overlay`, `ProgressiveList.from_ssz_bytes_fixed_total_spec_of_overlay`, and `ProgressiveList.from_ssz_bytes_variable_total_spec_of_overlay` give exact default-map criteria and total representation contracts. `from_ssz_bytes_trace` recovers actual consumed payloads; `from_ssz_bytes_success_iff` retains the execution-only criterion. Per-occurrence payload, empty-input, zero-width, malformed-offset, prefix-error, and roundtrip contracts remain in the coverage record |
| `Serialize::serialize` | Out of scope. Historical Serde protocol findings: issue 20 |
| `Deserialize::deserialize` | Out of scope. Historical visitor/sequence and error-order findings: issues 20 and 22 |
| `Deserialize::deserialize_in_place` | Out of scope, including the inherited default. Historical source audit: issue 20 |
| `Arbitrary::arbitrary` | `ProgressiveList.arbitrary_total_spec_of_overlay`, `ProgressiveList.arbitrary_success_spec_of_overlay`, `ProgressiveList.arbitrary_represents_iff`, `ProgressiveList.arbitrary_success_represents_iff`, `ProgressiveList.arbitrary_success_iff_inputs`; feature `arbitrary` |
| `Arbitrary::arbitrary_take_rest` | `ProgressiveList.arbitrary_take_rest_total_spec_of_overlay`, `ProgressiveList.arbitrary_take_rest_represents_iff`, `ProgressiveList.arbitrary_take_rest_success_represents_iff`, `ProgressiveList.arbitrary_take_rest_success_iff_inputs`; actual owning trait default, with its discarded final input recovered from the ordinary generator |
| `Arbitrary::size_hint` | `ProgressiveList.arbitrary_size_hint` |
| `Arbitrary::try_size_hint` | `ProgressiveList.arbitrary_try_size_hint` |
| `ContextDeserialize::context_deserialize` | Out of scope as Serde-based context deserialization, including its visitor/seed protocol; feature `context_deserialize`, issue 22 |

## Returned iterators and handles

| Rust method | Primary proof entry point, remaining obligation, or scope exclusion |
| --- | --- |
| `ProgressiveListIter::next` | Complete merged enumeration in `Tree/ProgressiveList/Iter/Next.lean`, consumed by the public constructor and collection contracts |
| `ProgressiveListIter::size_hint` | `ProgressiveListIter.size_hint_spec` |
| `ProgressiveListIter::len` | `ProgressiveListIter.exact_len_spec` |
| `ProgressiveListIter::fmt` | Out of scope: derived `Debug` |
| `ProgressiveListIterCow::next_cow` | Pending actual borrowed stepping, returned indices/handles, exhaustion, and write-back; issue 16 |
| `ProgressiveListIterCow::fmt` | Out of scope: derived `Debug` |
| `Cow::into_mut` | `milhouse.cow.Cow.into_mut_success_iff`, `into_mut_value_success_iff`, `into_mut_written_of_success`, and `into_mut_missing_entry`; `ProgressiveList.get_cow_into_mut_spec_of_materialization` proves list execution/replacement under exact entry/clone inputs, and `get_cow_into_mut_writeback_spec` recovers the footprint from actual successful calls |
| `Cow::deref` | Pending actual borrowed-field extraction; issue 9. The proved data observer is not this method |
| `Cow::make_mut` | Pending actual borrowed materialization and write-back; issue 9. Consuming `into_mut` is not this method |

The two iterator Debug derives were present in Rust but were not explicitly
named in the previous coverage row. They are now recorded as out of scope. No
iterator-formatting extraction was attempted in this audit; the existing list
formatter probe is not evidence that either iterator formatter elaborates.
The `debug` feature changes the bounds on `Value`; it does not gate these
three Debug derives.

`src/serde.rs` also exposes `ProgressiveListVisitor`. Its actual `Default`,
`expecting`, `visit_seq`, and inherited visitor dispatch/error behavior are
dependencies of the excluded Serde deserializer protocol and are also out of
scope. `AnyList` contains and dispatches to
`ProgressiveList`; a proved underlying method alone does not verify the wrapper.
Likewise, this inventory does not assert proofs of arbitrary standard-library
blanket conversions or iterator adapters from a proof of `next` alone.

## Result of the audit

The MaxMap mutable-wrapper checkpoint (`fec41a5`) adds eight public lemmas
for actual `get_mut_with`: exact initial result and continuation, success
equivalence, present/missing maximum behavior, pointwise lookup-frame transfer,
and missing-loan restoration. No inner maximum-query law, cloning, index bound,
or cache invariant is needed by the exact operational equations. All eight
proofs use only `propext` and `Quot.sound`. The 324 Rust library tests pass;
eight update-map tests were rechecked after the final local-name adjustment.

The actual `get_cow_with` and `get_cow_with_value` wrappers also extract and
compile, but their correctness contracts remain pending. Explicit Rust Option
matches and namespace-safe locals avoid the existing Aeneas borrowed-`Try`
and naming limitations while preserving behavior. Aeneas, external models/
templates, and prior generated function bodies are unchanged. The remaining
wrapper contracts, semantic-invariant and concrete dictionary composition,
borrowed CoW, and assumption/model review are still incomplete. Debug and
Serde are excluded; TreeHash remains deferred.

The full build passes (2,162 jobs), and the complete axiom/import audit
validates 6,207 declarations across 446 modules. Of these, 6,088 use only
standard axioms or none and 119 retain the existing Arc pointer contract.
No new nonstandard axiom dependencies are introduced.

The model dependency audit also passes for the unchanged 42 roots and 151
local declarations. All nine source-suite reports have current input hashes,
retaining 52 checked proofs; unchanged suites were not rerun.

The MaxMap wrapper review (`a5c77c3`, cache invariant `72dba6d`) adds
seventeen public lemmas for five actual source paths: default construction,
lookup, insertion, cardinality, and cached maximum. Exact insertion metadata
requires no inner maximum law, cache invariant, cloning, or successor bound.
A separate invariant bounds successful present reads and attains a present
cached key. Construction's validity is characterized by the actual inner
default outcome; insertion preserves it from the inner lookup frame. These
proofs advance the concrete wrapper's source coverage while retaining an
abstract inner `UpdateMap`. The remaining wrapper mutable/CoW, range, and
trait paths, concrete dictionary composition, borrowed CoW, and remaining
assumption/model review are still incomplete. Debug and Serde are excluded;
TreeHash is deferred.

All seventeen public lemmas pass individual axiom checks: five are axiom-free
and twelve use only standard Lean axioms. The eight existing update-map Rust
tests pass. Extraction adds only cfg-gated callers and their source bodies;
existing Rust and extracted method bodies, external templates/models, and
Aeneas remain unchanged.

The full build passes (2,161 jobs), as does the complete axiom/import audit:
6,190 declarations across 445 modules, with 6,071 using only standard axioms
or none and 119 retaining the existing Arc pointer contract. No new
nonstandard axiom dependencies are introduced.

The model dependency gate passes for the unchanged 42 roots and 151 local
declarations. SSZ and Arbitrary source suites pass after rerunning against the
regenerated type file. All nine reports have current input hashes, totaling
52 source-contract proofs (20 axiom-free, 32 standard-only); the seven
unaffected suites were not rerun.

The concrete VecMap source review (`ad39a6d`, invariants `235382e`) adds
thirteen proofs against independently extracted source for
construction, cardinality, emptiness, indexed lookup, and mutable lookup,
including the two actual Option borrow helpers. Four native tests pass. The
count invariant is established by construction and preserved by mutable loans;
lookup equations require no count invariant or cloning. This advances the
fidelity of the default map's dependencies without claiming a complete
`UpdateMap` instance. Insertion's iterator-signature failure is reproduced in
UPSTREAM_BUGS 28; range/max operations, entry footprints, and `MaxMap`
composition still need their own work.

All nine source suites pass with explicit source-crate validation, totaling
52 checked proofs (20 axiom-free, 32 standard-only); all report input hashes
were current at that checkpoint. Its main `Tree` proofs and included-root
inventory were unchanged, so the previous 6,163-declaration/443-module audit
and 42-root/151-declaration model inventory were not rerun then. Borrowed CoW
and remaining assumption/model review are still incomplete. Debug and Serde
are excluded; TreeHash is deferred.

The consuming materialization review (`8bb4bb4`, list contracts `477cdb3`)
proves the exact entry/clone conditions for `Cow.into_mut`, including vector
growth bounds and the actual initial value. Successful execution supplies the
filled-entry footprint. The list's success criterion and complete replacement
contract now use those conditions without entry-key equality or a law
classifying pending handles as mutable; older signatures remain adapters.

All ten new public lemmas use only standard Lean axioms. The full build and
axiom/import audit pass for 6,163 declarations across 443 modules: 6,044 use
only standard axioms or none and 119 retain the existing Arc pointer contract.
This proof-only change leaves Rust, extraction, external models, and Aeneas
unchanged. Borrowed CoW and remaining assumption/model-fidelity review stay
open; Debug and Serde are excluded and TreeHash is deferred.

The CoW fallback review (`c7310ef`, exact criteria `5ad99dc`) removes the
requirement that map laws hold for every possible optional fallback. Read,
release, entry-location, occupied-handle, write-read, and maximum-result laws
are restricted to the value selected by this list's actual input lookups.
The proofs preserve all sixteen original public theorem names/signatures.
The selected-fallback read and release laws are also proved necessary, with
no representation, cloning, termination, or structural assumptions.

All fifteen new public lemmas use only standard Lean axioms. The full build
and axiom/import audit pass for 6,147 declarations across 440 modules: 6,028
use only standard axioms or none, and 119 retain the existing Arc pointer
contract. No Rust, extraction, external model, or Aeneas source changed; the
eight source suites and unchanged 42-root/151-declaration dependency gate were
not repeated for this proof-only work. Borrowed CoW and remaining assumption/
model-fidelity work stay open. Debug and Serde are excluded; TreeHash is deferred.

The mutable fallback review (`06e66dc`, exact criteria `dfdc682`) removes the
requirement that mutable-map laws hold for every possible fallback closure.
The read, write-read, maximum-result, and missing-handle laws now apply only
to the dictionary and environment actually supplied by this list's `get_mut`.
Thirteen weaker theorems cover acquisition, initial value, element replacement,
length, and missing-index restoration; the original eighteen theorem names
and signatures remain available, with their stronger contracts specialized
through adapters. Three further equivalences characterize a specified returned
value, successful acquisition, and the exact clone-termination condition for
an actually present immutable read. The acquisition criteria require only
the read law at this fallback, without representation, structural, write,
metadata, or clone laws upfront.

All sixteen new public lemmas use only standard Lean axioms. The full build
and axiom/import audit pass for 6,130 declarations across 434 modules: 6,011
use only standard axioms or none, and 119 retain the existing Arc pointer
contract. No Rust, extraction, external model, or Aeneas source changed; the
eight source suites and 42-root/151-declaration dependency gate were not
repeated for this proof-only change. Borrowed CoW and remaining assumption/
model-fidelity work stay open. Debug, Serde, and TreeHash remain out of scope.

The core adapter review in `7b2939e` adds axiom-free source comparisons for
`Result::map_err`, `hint::must_use`, and blanket `Borrow::borrow`, all referenced
by included API roots. Error-mapping callbacks may succeed, fail, or diverge;
no callback or clone law is assumed. The core suite passes seven comparisons
and eleven native tests. The full library/axiom audit still passes for 6,103
declarations across 429 modules. The unchanged other source suites were not
rerun; those reports together contain 39 comparison proofs. This reduces
model-fidelity gaps without changing public-operation coverage or closing the
borrowed CoW extraction obligations.

The power model review in `eb2f91b` adds a
[parameterized source comparison](reproducers/pow_models/README.md) for the
complete `usize::pow` body, including both permitted compiler-selector
branches and overflow. It uses only standard Lean axioms and assumes no
arithmetic bound or termination. The selector itself and existing scalar
primitives remain explicit boundaries. All eight source suites pass with
36 comparison proofs; the full axiom/import audit passes for 6,103 theorem
declarations across 429 modules, and the dependency gate passes for 42 roots
and 151 local model declarations. Public-operation coverage and the remaining
borrowed CoW obligations are unchanged. Debug, Serde, and TreeHash remain
outside the current goal.

The binary selection necessity review (`3cf17f1`, progressive/list necessity
`22b4d2f`, binary necessity `453ef4c`) removes the remaining upfront numeric
binary selection condition from the materialization criteria. Successful
selected children rebuild to nonzero trees; dense output therefore forces their
lengths positive. Binary `Selection.lean` proves that every selected query starts
inside the final occupied window, using layout, prefix alignment, successful
execution, and output density. It needs no input invariant, offset alignment,
capacity, clone, range-value, or termination law. A clipped-prefix corollary
converts the local occupied length to a global logical endpoint.

`ProgressiveTree/BulkUpdate/BinarySelection.lean` recovers both an actual
successful binary result and its exact clipped dense length at each selected
layer. It then lifts numeric selection necessity to recursive and public
progressive rebuilding. `ApplyUpdates/BinarySelection.lean` derives the condition
from successful nonempty application and dense output alone, with layout but
without input representation/backing, output capacity, default, clone, range,
or termination assumptions.

The new successful-result criterion in `SkippedConditions.lean` needs only
layout and input representation/backing validity upfront. Selected clone
identity, numeric selection, and all skipped-value agreements are jointly
necessary and sufficient for valid materialization after actual success.
`InputConditions.lean` gives four exact existence criteria, with or without
final representation and across both branches. Positive binary selection is
now on the necessary-and-sufficient side alongside reached-query termination,
`BulkCloneLaws`, missing-update guards, progressive selection, all skipped-value
agreements, final occupied capacity, and actual default construction. The
representation variants additionally require the actual default map's exact
extent and self-overlay.

No separate clone, range, termination, guard-success, final-capacity, or
default-success law is assumed upfront by those existence criteria. Layout and
input representation/backing validity remain the explicit rebuilding
preconditions. The no-op needs valid backing already storing the contents and
no rebuilding conditions; its representation variant uses input representation.
All existing public theorem names remain available. This closes binary
selection necessity for these materialization contracts; it does not establish
raw success alone implies density or complete the remaining input/geometry
and model-fidelity audits.

Focused and full builds pass (2,145 jobs). The axiom/import audit covers
6,103 declarations across 429 modules: 5,984 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All 11 new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing execution, total, and cache
proofs validate.

Work remains on geometry and input assumptions, borrowed CoW, and model
fidelity. No Rust, extraction, external model, or Aeneas source changed; the
seven source suites and 42-root/151-declaration dependency gate were not
repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
is deferred outside the goal.

Previous skipped-binary materialization checkpoint:

The skipped-binary materialization review (`5108135`, successful-result
criterion `92b365d`, total contracts `a8455fa`, progressive/list contents
`24607a2`, selected-layer reads and scope `3a7d3ce`) removes pending-value
exclusion and reflection from selected-layer read-back, progressive contents,
list materialization, and complete total correctness. Matching redundant updates
may now be skipped inside binary windows as well as progressive layers and
maximum-skipped suffixes. The conditions refer to actual input observations and
original slots, without assuming a rebuilding result.

The generalized layer and progressive contents proofs use binary skipped-value
agreement alongside retained/pending clone identity and the existing progressive
layer/suffix agreements. `ApplyUpdates/Contents.lean` derives every final backing
read without density or default-map laws. `Materialized.lean` combines these
reads with the weaker backing-density contracts to identify the exact stored
sequence. The new nonempty and all-branch `_total_spec_of_guards` contracts
also derive execution, representation, backing validity, and the pending
observer, under the actual default map's extent, overlay, and emptiness laws.
The older sufficient contracts retain their signatures as adapters.

`SkippedConditions.lean` characterizes valid materialization after actual
nonempty success by retained/pending identity, positive progressive selection,
and agreement in all three skipped scopes. No clone or range-value law is
assumed upfront. Layout, input representation/backing validity, and positive
numeric binary selection remain explicit. The default map is unconstrained.

`SelectionConditions.lean` gives four exact existence criteria for valid
materialization, with or without final representation, on the nonempty branch
and across both branches. Occupied capacity, reached-query termination, copied
storage termination plus retained/pending identity, missing-update guards,
positive progressive selection, all skipped-value agreements, and actual default
construction are on the necessary-and-sufficient side. No range-value reflection
or upfront clone, termination, guard-success, or default-success law is required.
Final occupied capacity is part of the criterion. Representation additionally
requires exact default-map extent and self-overlay. The no-op requires valid
backing already storing the contents, with no rebuilding conditions; its
representation variant uses input representation.

Positive numeric selection inside binary subtrees remains an upfront condition
on rebuilding: a true answer must select a window starting inside the final
prefix. Proving this condition necessary and moving it into the exact criterion
is unfinished. These results do not claim that raw success alone establishes
valid backing or correct contents, or that all hypothesis audits are complete.

Focused and full builds pass (2,141 jobs). The axiom/import audit covers
6,069 declarations across 425 modules: 5,950 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All 19 new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing execution, total, and cache
proofs validate.

Work remains on binary selection necessity, geometry and other assumptions,
borrowed CoW, and model fidelity. No Rust, extraction, external model, or Aeneas
source changed; the seven source suites and 42-root/151-declaration dependency
gate were not repeated for this proof-only work. Debug and Serde remain excluded;
TreeHash is deferred outside the goal.

Previous binary density range checkpoint:

The binary density range review (`82f8265`, binary skipped extents `4446f3e`,
progressive/list numeric contracts `3bbf03b`, binary density `a44efeb`, local
reflection adapter `0fefbab`) removes pending-value range reflection from
backing-density preservation. Reached ranges need only numeric effects:
skipped windows keep their occupied length, and selected windows start inside
the final prefix. The generalized binary proof clips global prefix endpoints
to each child window. The prior binary, progressive, and list reflection
contracts retain their signatures as adapters.

`Tree/BulkUpdate/SkippedExtents.lean` derives false-answer extent preservation
from agreement with original dense slots. Otherwise a newly required extension
value would have to match a missing old slot. This uses input density, prefix
alignment, and local monotonicity/extension completeness, without an update
result, packing-operation law, machine-capacity bound, clone law, or range-value
law. Its density corollary combines that agreement with numeric positive
selection. `ProgressiveTree/BulkUpdate/BinarySkippedExtents.lean` lifts the
false-answer result through selected-layer slot routing using input density,
layout, and the extension laws, without input capacity or successful rebuilding.

The new progressive density and list backing contracts accept numeric conditions
for both progressive and binary ranges. Their skipped-range variants derive all
false-answer extent conditions from agreement with original values, leaving only
positive numeric selection independent. `apply_updates_preserves_backing_of_skipped_ranges`
proves backing validity on every successful application from input representation
and backing validity, with layout and reached range conditions only on the
rebuilding branch. Representation supplies the dense update domain, and actual
checked length supplies the maximum's numeric bound. No clone identity,
clone termination, range termination, or default-map law is assumed.

These are preservation theorems conditional on actual success. The separate
execution criteria use the previously proved missing-update guards without
range correctness. The public valid-materialization existence criteria still
retain selected binary reflection: the weaker binary content conditions must
be lifted through the progressive/list sufficient proofs and combined with
these density contracts. Necessity of the remaining binary numeric selection
conditions also needs proof. Correct stored contents, valid backing, and
successful execution remain distinct obligations.

Focused and full builds pass (2,139 jobs). The axiom/import audit covers
6,051 declarations across 423 modules: 5,932 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All 14 new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing execution, total, and cache
proofs validate.

Work remains on materialization criteria, selection necessity, geometry and
other assumptions, borrowed CoW, and model fidelity. No Rust, extraction, external
model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous execution-guard checkpoint:

The missing-update guard review (`d1c91b1`, progressive contracts `676a3a5`,
binary contracts `2998487`, necessity `2224494`, scope `bcefc21`) removes
range correctness from binary, progressive, and public list execution proofs.
`BulkGuardsPass` states the actual missing-update checks: an unpacked terminal
needs a pending value; an internal node cannot have both child queries return
false, and selected children must pass their own guards. Packed terminals need
no pending-value witness. This condition uses input geometry and actual map
answers, without assuming an update result or query termination.

Successful binary execution implies these guards under layout, input shape,
and prefix alignment, without range, clone, termination, density, or capacity
laws. Selected-layer scopes lift necessity to progressive rebuilding and list
application. The generalized sufficient execution proofs use these guards and
reached-query termination instead of binary range reflection. Previous
`_of_enabled` contracts retain their signatures as adapters from their stronger
pending-witness and reflection laws.

`ApplyUpdates/GuardConditions.lean` proves exact execution criteria for nonempty
application and both branches. On the rebuilding branch, input representation,
density, layout, occupied capacity, and selected clone termination remain
upfront. Reached range-query termination, selected guards, and an actual
successful default construction are on the necessary-and-sufficient side.
No range correctness, assumed guard success, or upfront query/default success
is required. The empty-map no-op has no rebuilding conditions.

These are execution criteria. The existing binary contents criterion separately
uses retained/pending clone identity and skipped-value agreement without range
correctness. Public valid-materialization criteria still use selected binary
reflection: weakening backing-density preservation and connecting the weaker
content conditions remain unfinished. Successful execution alone does not
establish valid backing or correct stored contents for incoherent map answers.

Focused and full builds pass (2,136 jobs). The axiom/import audit covers
6,008 declarations across 420 modules: 5,889 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All 19 new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing success, total, and cache
proofs validate.

Backing-density range premises, geometry and other assumption minimality,
borrowed CoW, and model fidelity remain unfinished. No Rust, extraction,
external model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous binary skipped-value checkpoint:

The binary skipped-value review (`30c17f3`, binary equivalence/selected
content bridge `8d17355`, generalized contents `7a2235e`, scope/routing
`79282b8`) weakens content preservation from exclusion of pending values in
skipped binary ranges to agreement with their original slots. Matching redundant
updates may be skipped. The condition uses only the original tree, geometry,
and reached range answers, without any rebuilding result. The generalized
shape/capacity/content and extracted read-back contracts accept this weaker
law; existing exclusion contracts remain adapters with unchanged signatures.

Actual successful binary rebuilding preserves every slot in a reached range
answered false. This uses layout and prefix alignment, without input shape,
density, capacity, offset alignment, range, clone, or termination laws. Correct
binary contents therefore force skipped-value agreement. Combined with retained
clone necessity, `with_updated_leaves_contents_iff_clones_skipped` characterizes
correct binary contents by retained/pending identity and skipped-value agreement,
with no range-correctness law in either direction. Layout, input shape, alignment,
and actual successful execution remain explicit in the equivalence.

The selected progressive content bridge and progressive/list `BinarySkipped.lean`
modules lift agreement necessity to successful dense list materialization.
Progressive necessity needs layout and correct mathematical slots, with no input
shape or density law. List necessity derives those slots from input representation
and backing validity plus dense output storing the exact contents; no output
capacity, range, maximum, default, clone, or termination law is assumed.
These results do not yet remove selected binary reflection from public
valid-materialization existence criteria: binary execution and backing-density
proofs still use it.

Focused and full builds pass (2,131 jobs). The axiom/import audit covers
5,962 declarations across 415 modules: 5,843 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All 19 new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing success, total, and cache
proofs validate.

Remaining binary execution/density range premises and geometry minimality,
borrowed CoW, and model fidelity are unfinished. No Rust, extraction, external
model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous progressive/list clone-identity checkpoint:

The progressive/list clone-identity review (`6f2915e`, list necessity
`5e01cf9`, progressive necessity `18b4833`, selected slots `b1246e7`) proves
that successful dense materialization forces every selected pending clone and
retained stored clone to preserve its value. Selected-slot routing recovers
both the original binary input and its actual rebuilt result without shape,
density, range, clone, or termination laws. Progressive necessity uses layout,
input shape, and correct mathematical suffix slots, with no capacity law.
At the list boundary, input representation and backing validity supply the
overlay; output density and exact stored contents supply correctness, without
assuming output capacity validity or any range, maximum, default, or clone law.

Four public existence criteria now assume no clone or termination law upfront.
Selected `BulkCloneLaws` appear on the necessary-and-sufficient side, combining
termination of all copied storage with identity only for retained slots and
pending values. Overwritten stored copies may change value. Query termination,
start, occupied capacity, positive progressive selection, skipped-layer/suffix
agreement, and actual default construction remain part of the criterion.
Selected binary reflection, layout, and input invariants remain upfront.
The representation variants add exact default-map extent and self-overlay;
the no-op requires valid backing already storing the contents and no rebuilding
laws. Output backing validity remains part of the result, so stored-list
equality alone is a weaker observation.

Focused and full builds pass (2,125 jobs). The axiom/import audit covers
5,897 declarations across 409 modules: 5,778 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All ten new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing success, total, and cache
proofs validate.

Binary range and geometry minimality, borrowed CoW, and model fidelity remain
unfinished. No Rust, extraction, external model, or Aeneas source changed;
the seven source suites and 42-root/151-declaration dependency gate were not
repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
is deferred outside the goal.

Previous binary clone-identity checkpoint:

The clone-identity review (`c3b836b`, terminal/routing lemmas `ba2a10c`,
packed identity `e6ea416`, actual clone tracking `1bc9b38`) proves that correct
binary update contents force identity for every selected pending clone and
retained stored clone. Actual vector/packed reads preserve the returned clone
values without identity or termination assumptions. Packed-window correctness
is exactly retained/pending identity; overwritten stored copies need no
identity law. The binary proof follows selected children and zero expansion,
using layout, input shape, and alignment, without range correctness, density,
capacity, clone, or termination laws. Under exclusion of pending values from
skipped binary windows, the existing converse gives an equivalence.

These are lower-level results. Propagating identity necessity to progressive
and list materialization remains unfinished; the public existence criteria
still assume retained/pending identity, selected binary reflection, layout,
and input invariants. Their previously derived query/stored-clone termination
and start conditions remain on the necessary-and-sufficient side, alongside
capacity, selection, skipped-value agreement, and actual default construction.
No rebuilding law is added to the no-op branch.

Focused and full builds pass (2,121 jobs). The axiom/import audit covers
5,875 declarations across 405 modules: 5,756 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. All 13 new public lemmas
use standard Lean axioms; private/generated declarations are included in the
inventory. No new axiom or admission was introduced. External axiom use is
unchanged, and `size_of` remains unused. Existing success, total, and cache
proofs validate.

Remaining progressive/list identity, binary range, and geometry minimality,
borrowed CoW, and model fidelity are unfinished. No Rust, extraction, external
model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous query-termination checkpoint:

The query-termination review (`09b6d34`, progressive/list necessity `ceb502f`,
complete scope `0095ccd`, binary necessity and geometry-step helper `b6b4338`)
proves that successful rebuilding certifies every reached range query.
`BulkRangeOn` is exactly the union of progressive layer queries and queries
inside selected binary layers. Progressive layer termination needs no metadata,
input invariant, clone, or range-correctness law; empty layer windows do not
call the external map. Binary necessity needs layout and prefix alignment, with
no shape, density, capacity, clone, lookup, or range-correctness law. Complete
progressive and public list necessity need only layout on nonempty application.

Four public existence criteria now remove the upfront query-termination law.
Termination of reached queries joins stored-clone termination, start, occupied
capacity, positive selection, skipped-layer/suffix agreement, and an actual
default outcome on the necessary-and-sufficient side. The criteria cover valid
materialization, with or without final representation, on the rebuilding branch
and across both branches. The remaining upfront clone/range laws are identity
on retained slots and selected pending values and reflection in selected binary
subtrees; layout and input invariants remain explicit. Final representation
adds exact default extent and self-overlay; pending emptiness is a separate
observer law. The no-op needs valid backing already storing the contents and
no rebuilding query or clone condition; its representation variant uses input
representation. Output backing validity is included, so equality of stored
lists alone is a weaker observation.

Focused and full builds pass (2,118 jobs). The axiom/import audit covers
5,818 declarations across 402 modules: 5,699 use only standard Lean axioms or
none, and 119 use the existing Arc pointer contract. The 11 new lemmas and
newly public geometry-step helper use standard Lean axioms; private/generated
declarations are included in the inventory. No new axiom or admission was
introduced. External axiom use is unchanged, and `size_of` remains unused.
Existing success, total, and cache proofs validate.

Remaining retained-identity, binary range, and geometry minimality, borrowed
CoW, and model fidelity are unfinished. No Rust, extraction, external model, or
Aeneas source changed; the seven source suites and 42-root/151-declaration
dependency gate were not repeated for this proof-only work. Debug and Serde
remain excluded; TreeHash is deferred outside the goal.

Previous skipped-layer agreement checkpoint:

The skipped-layer review (`5a9398e`, read criterion `5481b38`, necessity
`84224a8`, capacity geometry `f146b17`, contents `b53be68`/`bacc216`,
bounds/scope `f3248ed`/`2f3e7bc`) allows pending values in a progressive layer
skipped by a false range answer when they match unchanged backing reads.
The lower proof derives complete read preservation from actual traversal;
its necessity direction needs no input representation, packing, shape, clone,
range-correctness, or default-map law. With the remaining selected clone and
binary range laws, correct backing reads are equivalent to agreement in both
skipped layers and maximum-skipped suffixes. Under numeric layer extents and
selected binary reflection, exact stored materialization has the same
criterion. Neither equivalence assumes agreement upfront or constrains the
installed default map. Existing stronger contracts are adapters. The
success/total and cache contracts validate but still use stronger range laws.

Focused and full builds pass (2,097 jobs). The axiom/import audit covers
5,667 declarations across 381 modules: 5,548 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All 22 new named lemmas use
only standard Lean axioms; private/generated helpers are included in the
inventory. External axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused. No Rust, extraction, external model,
or Aeneas source changed; the seven source suites and 42-root/151-declaration
dependency gate were not repeated for this proof-only work. Necessity of the
numeric layer extents, binary range/clone/geometry minimality, borrowed CoW,
and model fidelity remain unfinished. Debug and Serde remain excluded;
TreeHash remains deferred.

Previous layer-range checkpoint:

The layer-range review (`3780516`, density `2416785`, empty-layer bounds
`01415b8`, scope `78cacde`) weakens four public contracts for backing
preservation, occupied-capacity certification, and representation from actual
rebuilt values. Progressive layers need only numeric occupied-length
conditions: skipped intervals retain their length, and selected intervals
start inside the final prefix. Reflection is confined to binary queries in
selected subtrees. The scopes follow actual input geometry and range/maximum
guards, with no assumed rebuilding result. Existing reflection contracts are
adapters using the represented input's dense update domain. Content,
materialization, and termination contracts still use stronger range laws;
those contracts and the cache contracts validate.

Focused and full builds pass (2,093 jobs). The axiom/import audit covers
5,630 declarations across 377 modules: 5,511 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All 21 new named lemmas use
only standard Lean axioms; private/generated helpers are included in the
inventory. External axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused. No Rust, extraction, external model,
or Aeneas source changed; the seven source suites and 42-root/151-declaration
dependency gate were not repeated for this proof-only work. Necessity of the
numeric layer conditions, binary range/clone/geometry minimality, borrowed
CoW, and model fidelity remain unfinished. Debug and Serde remain excluded;
TreeHash remains deferred.

Previous apply-updates materialization checkpoint:

The materialization review (`dda608d`, equivalence `034d26b`, suffix reads
`19dee5c`) proves skipped-value agreement necessary for exact materialization.
The lower proof preserves complete read results through every actual skipped
suffix without packing, shape, clone, or range-correctness assumptions. The
public necessity result needs neither input representation nor default-map
laws. Under selected clone/range and backing laws, agreement is equivalent
to correct backing reads and exact stored contents. Successful materialization
has an exact occupied-capacity/agreement/default-construction criterion;
the combined representation criterion adds actual default overlay and extent.
Agreement and default success are derived in the forward direction. The public
no-op stores the target sequence exactly when its input backing already does;
all rebuilding laws apply only on nonempty application. `Conditions.lean`
now reuses the combined criterion. Necessity concerns materialization; the
separate representation criterion permits compensation by the installed map.

Focused and full builds pass (2,091 jobs). The axiom/import audit covers
5,600 declarations across 375 modules: 5,481 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All 10 new named lemmas use
only standard Lean axioms; private/generated helpers are included in the
inventory. External axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused. Existing sequence, total, and cache
contracts validate. No Rust, extraction, external model, or Aeneas source
changed; the seven source suites and 42-root/151-declaration dependency gate
were not repeated for this proof-only work. Selected clone/range and geometry
minimality, borrowed CoW, and model fidelity remain unfinished. Debug and
Serde remain excluded; TreeHash remains deferred.

Previous apply-updates skipped-suffix checkpoint:

The skipped-suffix review (`10c8634`, list contents `592280c`, bulk contents
`ad51425`, scope `25f577f`) generalizes content preservation, materialization,
total correctness, and public success/representation criteria. The new
`BulkSkippedValuesAgree` law permits pending entries beyond the reported
maximum when they agree with the unchanged backing. It concerns only present
values inside the new logical prefix and suffixes selected by the actual
geometry/range/maximum guards; it assumes no rebuilding result. The checked
length supplies the numeric extension bound. Exact default-map overlay and
extent remain in the total and sequence criteria, with pending emptiness
separate. All work laws apply only on nonempty application. Existing
semantic-maximum and empty-map contracts are adapters; cache contracts validate.

Focused and full builds pass (2,088 jobs). The axiom/import audit covers
5,583 declarations across 372 modules: 5,464 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All 15 new named lemmas use
only standard Lean axioms; generated helpers are included in the inventory.
External axiom use is unchanged. No new axiom or admission was introduced,
and `size_of` remains unused. No Rust, extraction, external model, or Aeneas
source changed; the seven source suites and 42-root/151-declaration dependency
gate were not repeated for this proof-only work. Necessity of the remaining
selected clone/range/skipped-value premises, geometry minimality, borrowed CoW,
and model fidelity remain unfinished. Debug and Serde remain excluded;
TreeHash remains deferred.

Previous apply-updates maximum-premise checkpoint:

The maximum-premise review (`aa023cf`, lower proofs `f0daba3`) removes
`MaximumBoundsValues` from five existing public lemmas: backing preservation,
both occupied-capacity criteria, and both representation criteria using the
actual rebuilt values. The actual checked length calculation supplies the
numeric bound required by the generalized bulk-density proof. Three new lower
lemmas retain the old semantic-maximum contracts as adapters. Content
preservation, materialization, and total sequence contracts still require
the semantic maximum law to justify skipped pending values; that review is
unfinished. Existing total and cache contracts validate.

Focused and full builds pass (2,087 jobs). The axiom/import audit covers
5,566 declarations across 371 modules: 5,447 use only standard Lean axioms or
none, and 119 use the existing pointer contract. The three new lower lemmas
and five strengthened public lemmas use only standard Lean axioms; generated
helpers are included in the inventory. External axiom use is unchanged. No
new axiom or admission was introduced, and `size_of` remains unused. This
proof-only work changed no Rust, extraction, external model, or Aeneas source;
the seven source suites and 42-root/151-declaration dependency gate were not
repeated. Borrowed CoW and the remaining assumption/model-fidelity audit are
unfinished. Debug and Serde remain excluded; TreeHash remains deferred.

Previous apply-updates overlay checkpoint:

`ApplyUpdates/Overlay.lean` characterizes representation from actual rebuilt
values and default-map overlay/extent, without separate clone identity or
empty-default laws. `Contents.lean` derives actual backing reads independently
of the default map; `Materialized.lean` establishes the stored sequence under
selected clone preservation. `Total.lean` uses exact default-map laws for its
complete representation/backing/observer contracts, with existing empty-map
contracts retained as adapters. Under the stated selected clone and metadata
laws, `Conditions.lean` characterizes successful preservation by the actual
empty-map no-op or occupied final capacity and an actual default outcome with
the exact overlay/extent. Pending emptiness supplies only its observer. The
representation and success criteria require all rebuilding laws only on the
nonempty branch. `len_after_apply_updates_iff` independently characterizes
complete length-result equality without representation or geometry, including
unchanged failure/divergence on the no-op branch. Length integration is
`8e80e9c`, success criteria `5823c1f`, total contracts `40ac435`, materialization
`decf6f7`, and overlay foundation `c338515`. Remaining clone/range/geometry
minimality and model fidelity are separate obligations.

Focused and full builds pass (2,087 jobs). The axiom/import audit covers
5,558 declarations across 371 modules: 5,439 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All nine new named lemmas use
only standard Lean axioms; generated helpers are included in the inventory.
External axiom use is unchanged. No new axiom or admission was introduced,
and `size_of` remains unused. Borrowed CoW and the remaining assumption/model-
fidelity audit are unfinished. Debug and Serde remain excluded; TreeHash is
deferred outside the current goal.

`Arbitrary/Overlay.lean` gives the actual default map's exact representation
criterion, and `Conditions.lean` combines finite control/element traces,
occupied-layer `LengthFits`, and default outcomes for exact public success
and sequence-preservation criteria. Neither trace nor default success is a
premise. `Traits.lean` proves the corresponding criteria for the actual owning
default, recovering the final input discarded by its ordinary generator call.
Element generators may consume, retain, or replace input. Generalized total
and successful-state contracts derive representation and valid backing/spine
under exact overlay/extent laws; pending emptiness supplies only its observer.
Existing empty-map contracts remain adapters. Owning integration is `16befa3`,
ordinary success and total contracts `f93004f`, and representation foundation
`b8f058f`. Packing geometry, remaining premise minimality, and external-model
source fidelity remain separate obligations.

Focused and full builds pass (2,084 jobs). The axiom/import audit covers
5,547 declarations across 368 modules: 5,428 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All nine new lemmas use only
standard Lean axioms; external axiom use is unchanged. No new axiom or
admission was introduced, and `size_of` remains unused. Borrowed CoW and the
remaining assumption/model-fidelity audit are unfinished. Debug and Serde
remain excluded; TreeHash is deferred outside the current goal.

`Decode/Overlay.lean` gives exact default-map overlay and extent conditions
for representation of the actual decoded sequence. `OverlayTotal.lean`
combines them with actual input-bound payload consumption and occupied-layer
`LengthFits` for an exact success and representation criterion. The trace is
recovered from successful execution; the complete trace total contract derives
execution, represented contents, valid backing, exact stored sequence/count,
and installed map. The fixed- and variable-format total contracts also use
these laws, with existing empty-map contracts retained as adapters. Pending
emptiness supplies only its observer. Empty bytes bypass packing and element
metadata; `represents_nil_iff` independently proves the empty sequence's exact
zero-length, absent-maximum, and absent-read conditions without tree or packing
premises. Public format integration is `decd3f9` (trace criteria `5c49998`,
representation foundation `5b8202a`). Geometry, codec-premise, and model-fidelity
review remain separate obligations. The subsequent Arbitrary checkpoint above
extends the default-map criteria to both generator entry points.

Focused and full builds pass (2,082 jobs). The axiom/import audit covers
5,538 declarations across 366 modules: 5,419 use only standard Lean axioms or
none, and 119 use the existing pointer contract. The nine named new lemmas
and two generated helpers use only standard Lean axioms; external axiom use
is unchanged. No new axiom or admission was introduced, and `size_of` remains
unused. Borrowed CoW and the remaining assumption/model-fidelity audit are
unfinished. Debug and Serde remain excluded; TreeHash is deferred outside the
current goal.

`Construction/Overlay.lean` characterizes representation for all four sequence
constructors using the actual default map's overlay and logical extent.
`OverlayConditions.lean` proves exact success and representation criteria
from finite consumption, occupied-layer `LengthFits`, and an actual default
outcome with these laws. Successful iterator calls supply their actual consumed
trace, proved equal to the stored sequence; vectors supply their own iterator.
Neither criterion needs pending emptiness. The generalized `Total.lean`
contracts derive execution, representation, backing validity, and spine
validity, with a separate emptiness law only for the pending observer.
Existing empty-map representation and total contracts are adapters. The
criteria are `a756c07` (total contracts `a32454f`, foundation `75701ea`). These
results audit default-map laws under the stated packing layout and geometry;
remaining premise minimality and model fidelity are not complete.

Focused and full builds pass (2,080 jobs). The axiom/import audit covers
5,527 declarations across 364 modules: 5,408 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All twelve new lemmas use
only standard Lean axioms; external axiom use is unchanged. No new axiom or
admission was introduced, and `size_of` remains unused. Borrowed CoW and the
remaining assumption/model-fidelity audit are unfinished. Debug and Serde
remain excluded; TreeHash is deferred outside the current goal.

`PopFront/OverlayTotal.lean` proves the exact public success-and-representation
criterion: nonzero removal needs the bound and retained capacity, actual
ordered clone outcomes, and an actual default map whose overlay/extent yields
the retained source suffix. Clone identity and empty-map reads/maxima are not
separate requirements. Zero removal omits clone/default laws, and layout and
backing laws apply only to a nonzero in-bounds rebuild. The complete nonzero
total result derives execution, representation, backing validity, exact cloned
contents, recorded length, and installed map; pending emptiness is a separate
observer law. `PopFront/Overlay.lean` gives the successful-result equivalence,
and `ProgressiveList/Overlay.lean` gives the underlying same-length dense
representation criterion. Existing dense-backing, front-removal content,
and total contracts are adapters to these results. Public integration is
`45f8783` (adapters `7801d06`, overlay foundation `9dd67d2`). The focused proofs
use only standard Lean axioms. This audits clone/default-map laws under the
stated geometry and representation premises; it does not establish full
premise minimality or model fidelity.

Focused and full builds pass (2,078 jobs). The axiom/import audit covers
5,515 declarations across 362 modules: 5,396 use only standard Lean axioms or
none, and 119 use the existing pointer contract. All five new lemmas use only
standard Lean axioms; external axiom use is unchanged. No new axiom or
admission was introduced, and `size_of` remains unused. Borrowed CoW and the
remaining assumption/model-fidelity audit are unfinished. Debug and Serde
remain excluded; TreeHash is deferred outside the current goal.

`Rebase/Lookup.lean` establishes exact full-result in-place reads, including
map failure/divergence and out-of-range indices, without representation or
map-read-success premises. Nonmutating lookup equality is equivalent to the
actual cloned map's answers agreeing at the original backing fallback.
`Representation.lean` proves in-place representation equivalence and makes
read/extent laws necessary and sufficient for the actual nonmutating clone to
preserve an already represented sequence. `SelectedTotal.lean` characterizes
successful sequence-preserving calls by backing readiness and, for nonmutating
rebase, an actual clone outcome with precisely those read/extent laws. Both
total contracts derive execution, represented contents, backing validity, and
metadata; existing content/total/cache contracts now use these results.
The public total checkpoint is `594f218` (representation `eef66e2`, lookup
`297cfd4`). Layout and backing geometry still justify indexed traversal, and
selected semantic content soundness remains explicit. The exact clone
criterion does not establish minimality of all other premises or model fidelity.

Focused and full builds pass (2,075 jobs). The axiom/import audit covers
5,510 declarations across 359 modules: 5,391 use only standard Lean axioms or
none, and 119 use the existing pointer contract. Ten new declarations reuse
that contract; no new axiom or admission was introduced, and `size_of` remains
unused. Existing downstream cache and validity contracts also validate.
Borrowed CoW and the remaining assumption/model-fidelity audit are unfinished.
Debug and Serde remain excluded; TreeHash is deferred outside the goal.

`Rebase/SelectedCaches.lean` gives general public cache criteria for both
rebase methods. Under selected `RebaseContentInputs` soundness and actual
success, result cache validity is equivalent to `RebaseCacheInputs`, without
layout, geometry, density, capacity, accurate-length, query-success, map,
or representation premises. Binary cache selection follows supplied optional
lengths and full depth, and cache-subject depth may be arbitrary. Progressive
selection follows actual packing queries and clamped lengths, with immediate
stops retaining the original suffix and no imported base progressive cache.
Existing cache contracts now use these results through dense-input adapters.
The action classifier is also generalized to supplied metadata, and its
reflection proofs now use only standard Lean axioms, without the pointer
contract. The public checkpoint is `e88ce19` (progressive `2307f24`, binary
`c20e293`, scopes `c31c8bb`, classifier `9db36ad`, axiom reduction `f9da88a`).
Cache-input necessity and sufficiency are conditional on the content law;
this does not finish semantic-premise minimality or the overall goal.

Focused and full builds pass (2,072 jobs). The axiom/import audit covers
5,497 declarations across 356 modules: 5,388 use only standard Lean axioms or
none, and 109 use the existing pointer contract. Five new cache-equivalence
declarations use that contract; the existing classifier no longer does.
No new axiom or admission was introduced, and `size_of` remains unused.
Borrowed CoW and the remaining assumption/model-fidelity audit are unfinished.
Debug and Serde remain excluded; TreeHash remains deferred outside the goal.

`Rebase/SelectedContents.lean` proves exact materialized backing-content
preservation for both public methods under the selected `RebaseContentInputs`
law and actual success. Its binary obligations use the actual supplied
optional lengths/full depth, and progressive obligations are conditional on
actual packing results with clamped layer lengths. No layout, density, shape,
capacity, accurate-length, comparison-termination, or query-success premise
is needed for this content result. The new `rebase_on_spec_of_content_inputs`
and `rebase_spec_of_content_inputs` preserve the merged sequence with the same
semantic law; geometry/layout still justify indexed traversal, and nonmutating
rebase retains fallback-aware clone reads and logical extent. Existing content
contracts now use these results through dense-input adapters. Semantic
soundness remains explicit; this does not establish necessity or finish the
assumption audit. The public integration checkpoint is `c8724e7` (public backing
results `78d9600`, progressive contents `b166ec0`, inputs `aa0bb68`, binary
foundations `1fa4dbc`, `47c372e`, and `5832bf5`).

Focused and full builds pass (2,065 jobs). The axiom/import audit covers
5,450 declarations across 349 modules: 5,345 use only standard Lean axioms or
none, and 105 additionally use the existing pointer contract. Eight additional
declarations reuse that contract; no new axiom or admission was introduced,
and `size_of` remains unused. Borrowed CoW extraction and the remaining
assumption/model-fidelity audit are incomplete. Debug and Serde remain
excluded, and TreeHash is deferred outside the current scope.

`Rebase/Ready.lean` proves complete public success criteria with no separate
packing-layout or global query-success premise. Missing or shared inputs
omit packing queries; entered node pairs require the actual factor and
defaulted-depth results and the selected arithmetic/geometry/element calls.
No positivity or power-of-two/coherence law is assumed. Nonmutating rebase
still needs the actual pending-map clone on tree shortcuts. The progressive
proof recovers query results from actual successful execution, and existing
total success proofs now use the complete public criterion. Query helper
outcomes remain explicit conditions; this is not a blanket metadata-totality
or source-fidelity claim. Packing and geometry for content/cache correctness
remain separate obligations.
At `3231f6f` (foundations `d1ba797`, `4952ade`, `cb7e79e`), focused and full
builds pass (2,060 jobs), and the axiom/import audit covers 5,430 declarations
across 344 modules. Seven additional declarations reuse the existing pointer
contract, for 97 total. No new axiom or admission was introduced; `size_of`
remains unused. The full goal remains incomplete.

The preceding `Rebase/SelectedConditions.lean` criteria cover both
public rebase variants, without whole-tree shape or representable-layer
assumptions. Under the original fixed-layout premise, selected depth/shape/shift
checks and element calls were jointly necessary and sufficient; nonmutating
rebase also required the actual pending-map clone to return. The requirements
retain both machine clamps in layer lengths, and pointer, zero-input, and
hash shortcuts omit unreached checks. All metadata and recursive successes
are derived. Existing progressive/public success lemmas now use the general
proof through invariant adapters, including the existing total contents/cache
contracts. Geometry for semantic correctness, packing assumptions, and model
fidelity remain separate obligations. These lemmas now require only actual
packing query results (`4952ade`); the complete criterion above also makes
those queries conditional on entered node pairs.
At `2d63438` (foundations `15af31a`, `9e1c78c`, `9afa364`, `dfe9e73`), focused
and full builds pass (2,057 jobs), and the axiom/import audit covers 5,399
declarations across 341 modules. Nine additional declarations reuse the
existing pointer contract, for 90 dependent declarations total. No new axiom
or admission was introduced. The full goal remains incomplete.

`Rebase/Conditions.lean` proves exact success criteria for both public rebase
variants. Under packing layout, compatible shapes, and representable original
layers, `rebase_on` succeeds exactly when its selected element comparisons
terminate; `rebase` additionally requires the actual pending-map clone to
return. No comparison success, density, accurate length metadata, semantic
equality/hash law, or map-preservation law is assumed. Binary and progressive
reflection recover the comparison scopes from actual successful calls,
including final pointer reuse, and the Arc/vector criteria retain every short
circuit. Binary reflection needs no geometry; progressive reflection needs
only layout and original capacity. These results audit comparison termination
under the stated geometry; the selected-input criteria above supersede that
restriction.
At `d5836d4` (foundations `3f2f4fa`, `c3ff39d`, `212ac40`), focused and full
builds pass (2,052 jobs), and the axiom/import audit covers 5,314 declarations
across 336 modules. Of 34 new declarations, 24 use only standard axioms or none
and ten reuse the existing pointer contract, for 81 dependent declarations
total. No new axioms or admissions were introduced. Remaining assumption
reviews, borrowed CoW, and model-fidelity obligations stay open.

`Rebase/CacheEquivalence.lean` proves the exact cache criterion for both public
rebase variants: a successful result has valid caches if and only if the
retained-original and imported-base cache laws hold together. Binary and
progressive reflection recover those laws from actual output validity,
including final pointer reuse. The equivalences retain the existing semantic
content laws and geometry, but assume no cache validity, represented sequence,
or pending-map clone/read/maximum law. At `ad4e3f4` (foundations `0dc26d2`,
`01b05f5`), focused and full builds pass (2,048 jobs), and the axiom/import audit
covers 5,280 declarations across 332 modules. The seven new operation lemmas
reuse the existing pointer contract, for 71 dependent declarations total;
no new axioms or admissions were introduced.

Original cache validity now follows two separate scopes: `RebaseOrigCachesOn`
for retained caches and `RebaseHashCachesOn` for reached hash-shortcut checks.
Eight successful-execution/total public cache contracts use these weaker
premises. Discarded original caches need no retention law, and unselected
original hash caches need no comparison-validity law. The error-inclusive
wrapper retains full original validity because errors restore the original;
cleared-input contracts derive both scopes internally. The progressive step
certificate retains child calls even when final pointer checks reuse the
original node. At `01f0d4f` (foundations `a653121`, `8173c77`), the full build
passes (2,045 jobs) and the axiom/import audit covers 5,257 declarations across
329 modules. All eleven public cache/validity contracts build. There are no
new axioms or admissions; the pointer-equality helper adds one use of the
existing pointer contract, for 64 total.

Binary action categories now select the base caches required by all eleven
public rebase cache/validity contracts. No-ops need no base validity;
whole-base replacement needs full base validity; rebuilding uses selected
child-cache laws. `KindReflection.lean` proves that the input classifier matches
every successful extracted rebase at accurate dense metadata, without element
or cache soundness or comparison-termination assumptions. The source's ordered
mixed-equality cases are retained. Binary/progressive preservation and both
finite-collision bridges use this scope, with full-base adapters retained.
At `99fad96` (foundation `b7e16e2`), focused and full builds pass (2,041 jobs),
and the axiom/import audit covers 5,235 declarations across 325 modules. There
are no new axioms or admissions; the reflection lemma adds one use of the
existing pointer contract, for 63 total. The original-cache refinement is
recorded above; remaining assumption/model-fidelity and borrowed CoW work
stay open.

The base-cache premise of all eleven public rebase cache/validity contracts is
`RebaseBaseCachesOn`. At the earlier progressive-layer checkpoint, validity
was required only in matching progressive
layers entered after pointer checks. Missing and shared suffixes are omitted;
adapters recover the new law from the earlier full-base invariants. The
progressive preservation and finite-collision proofs use the same scope.
That checkpoint still required full validity within each selected binary layer. At `1547078`
(foundation `e512df3`), focused and full builds pass (2,038 jobs), and the
axiom/import audit covers 5,141 declarations across 322 modules with no new
axioms or admissions and the same 62 pointer-contract dependencies.

Packed rebase soundness now constrains elements only if every paired `ne`
call returns false. `Rebase/PackedSoundness.lean` proves that this guarded
element law, conditional on equal vector lengths, is necessary and sufficient
for sound positive vector equality. The previous reached-pair law implies it.
Any true, failed, or diverging paired call removes all soundness obligations
for that vector, including earlier false answers. The binary rebase branch
equivalence and every dependent public contents/cache contract use the weaker
law, retaining pointer/hash shortcuts and separate termination assumptions.
At `fbf2a27` (foundation `e9ada7a`), focused and full builds pass (2,037 jobs);
the axiom/import audit validates 5,127 declarations across 321 modules, with
the same 62 pointer-contract dependencies and no new axioms or admissions.
This changes proof assumptions; model fidelity and borrowed CoW remain open.
Debug, Serde, and TreeHash remain outside the current scope.

The separate [Option source comparison](reproducers/option_models/README.md)
now validates eleven local models against freshly extracted pinned
standard-library bodies and one additional `cloned` composition, all without
axioms. Direct `cloned` extraction remains unsupported at its higher-ranked
function item. This reduces a trusted-model review obligation; it does not
change API coverage or complete the borrowed CoW proofs.

The [core source comparisons](reproducers/core_models/README.md) additionally
validate `Result::map_err`, `hint::must_use`, blanket `Borrow::borrow`,
`mem::take`, `usize::div_ceil`, `u128::saturating_mul`, and `u128::checked_pow` against their
actual extracted standard-library bodies, including arbitrary Default results,
zero divisors, saturation on overflow, and checked-power termination/overflow.
Error mapping preserves arbitrary callback results; the three adapter proofs
and `take` are axiom-free. Their source audit and all eleven native tests pass. Checked multiplication
remains an Aeneas foundation primitive; three
other numeric helpers retain missing intrinsic templates (UPSTREAM_BUGS issue
24). No production model or public-operation specification changed.

The separate [power comparison](reproducers/pow_models/README.md) now proves
the complete `usize::pow` body for either compiler-selector outcome. Its
intrinsic template remains unsupported, but a section parameter permits both
actual extracted loops to be checked without replacing their bodies.

The [fixed-byte source comparisons](reproducers/fixed_bytes_models/README.md)
also validate the actual pinned clone, equality, ZERO, default, and `is_zero`
bodies used by cache initialization and rebasing. All five match the local
models for every length and byte array without additional premises, retaining
the existing array/byte foundation. Their source audit and four native tests
pass, alongside the core and Option suites after extending the shared runner
for locked dependencies and constant-initializer provenance. Public API
coverage and the scope exclusions are unchanged.

The [tuple source comparisons](reproducers/tuple_models/README.md) validate
`eq`, `ne`, `partial_cmp`, and `cmp` for arbitrary callback results, without
consistency or termination premises. Four native tests cover 59 answer
combinations, dispatch, and call order. The runner verifies that omitting four
unused unsupported trait defaults leaves every compared source declaration
unchanged. All four source suites pass at `c948ef8`, totaling 24 direct
comparisons and the separate Option cloned composition: 25 proofs, 16
axiom-free and nine standard-only. The main proof/dependency inventories are
unchanged; borrowed CoW and remaining model/assumption review stay open.

The [vector source comparisons](reproducers/vec_models/README.md) add three
checks for `is_empty`, `eq`, and `ne`, preserving arbitrary callback results
without consistency or termination assumptions. Checked name-only changes
to temporary LLBC expose actual source bodies suppressed by builtin matching;
all other fields must remain identical. The vector/index/slice foundations
remain trusted. At `1a575ec`, all five source suites pass: 27 direct comparisons
and one composition, totaling 28 proofs (16 axiom-free, twelve standard-only).
Six native vector tests pass. Direct `pop`/`next_back` extraction remains
unresolved at container field/type analysis (UPSTREAM_BUGS 25). The main
proof/dependency inventories and scope exclusions are unchanged.

The [SSZ comparisons](reproducers/ssz_offset_models/README.md) include two
direct checks for the actual four-byte constant and private decoder, plus a
separate composition check for the public reader's prefix slicing. All input
lengths, the full copy loop and termination, and exact error payloads are
covered without extra premises. All three proofs use only standard Lean
axioms. The runner checks that temporary root retention and source error-type
renaming leave every other LLBC field unchanged. Actual encoder construction
also matches the local model, including its release continuation, relative
to the existing `Vec::reserve` model. The audit imports that concrete primitive
and never compiles the generated axiom template; reservation fidelity remains
a boundary. At `4cbc263`, all seven source suites pass: 33 direct comparisons
and two compositions, totaling 35 proofs (16 axiom-free, nineteen standard-only).
Eight native SSZ tests pass. Direct public-reader extraction, offset encoding,
and encoder append/finalize remain unresolved (UPSTREAM_BUGS 26). The main proof/dependency
inventories and scope exclusions remain unchanged; borrowed CoW and the
remaining model/assumption review stay open.

The [Arbitrary source comparisons](reproducers/arbitrary_models/README.md)
validate collection control against the actual bool/byte generators and
one-byte copy/zeroing loop. For every input, the Boolean answer and exact
remaining input match, including consumed even stopping bytes and successful
false at exhaustion. There are no extra premises, and the proof uses only
standard Lean axioms. Both size-hint defaults also match their source for
arbitrary dictionaries and depths, preserving actual callback results without
consistency or termination premises. Eight native tests additionally check
vector input replacement, error/panic short-circuiting, and default dispatch,
including hint-callback panics. Full vector generation and the owning Arbitrary
default remain source boundaries (UPSTREAM_BUGS 27). At `e396dad`, all seven
source suites pass: 32 direct comparisons and two compositions, totaling
34 proofs (16 axiom-free, eighteen standard-only). The main proof and
model-root inventories are unchanged; borrowed CoW and the remaining model
and assumption review remain open.

Append now uses exact observable lookup conditions. `AppendReadAgrees` in
`Push/Lookup.lean` requires the appended key to return the new pending value;
other keys need only agree after the original backing fallback, without raw
map-read equality. Its public-read equivalence preserves errors/divergence
and needs a backing bound only when querying the appended key. The new
boundary lemma proves public reads equal raw map answers beyond the backing
length. The old insertion/lookup law implies the new agreement contract.

`push_represents_append_iff` proves the lookup conditions and exact maximum
jointly necessary and sufficient for a successful push to represent the
appended sequence. No map-read law or separate capacity bound is assumed in
this equivalence. Existing indexed read-back, sequence, and total append
contracts use the weaker law, as does the metadata equivalence. The total proof
uses the joint criterion. `len_after_push_iff_max_index` retains the necessary exact maximum
condition. This audit concerns sequence contracts, not concrete map fidelity.
At checkpoint `2e4927d` (lookup foundations `79bd2a6`), the focused and full
builds pass (2,035 jobs), and the axiom/import audit validates 5,108 declarations
across 319 modules. All new and revised append results use only standard Lean
axioms; no new axioms or admissions were added. Rust and external models are
unchanged.

Mutable and consuming CoW write-back now use `GetMutWithWriteReads` and
`GetCowWithValueWriteReads`: raw map answers must agree with the replacement
and unchanged other reads after the actual backing fallback. Even the selected
replacement may come from that fallback. Adapters derive these contracts from
the old exact insertion/lookup laws for any backing function. The initial
read/clone contracts and actual CoW `Written` entry/metadata effects are retained.

`WriteBack.lean` proves raw lookup agreement and maximum-result agreement
jointly necessary and sufficient for an in-bounds `List.set` result.
`get_mut_represents_set_iff` and `cow_writeback_represents_set_iff` specialize
that criterion to actual returned continuations; existing sequence and total
specifications use the weaker laws. The pointwise read equivalences preserve
errors/divergence without bounds, representation, or write-law assumptions.
The CoW equivalences need no filled-entry footprint; the consuming proof still
derives the actual footprint and applies its conditional map law. The earlier
maximum-result laws and full length equivalences remain in use. At checkpoint
`7d329d7` (foundations `a027551`, `ac16012`), focused and full builds pass
(2,036 jobs), and the axiom/import audit validates 5,117 declarations across
320 modules. All new and revised write-back results use only standard Lean
axioms; no new axiom or admission was added. Rust and external models are
unchanged. Borrowed CoW methods and iterator stepping remain separate open
obligations.

The rebase observer contract drops maximum-index identity as well.
`UpdateMap/Length/Equivalence.lean` proves an exact criterion on raw maximum
query results: successful maxima may differ if they give the same mathematical
extent, and failure/divergence/overflow outcomes are retained. For example,
with backing length 10, `None`, `Some 0`, and `Some 9` all give length 10.
`rebase_observers_eq_iff` proves that this condition and equality of the actual
emptiness queries are necessary and sufficient for the two observer results
to agree. The revised preservation theorem assumes no map validity, indexed
read law, representation, or successful observer/query call. At checkpoint
`dab2f4e`, the focused and full builds passed, and the axiom/import audit
covered 5,070 declarations across 315 modules without new axioms or admissions.

Clone, clone_from, and dependent rebase sequence/cache contracts now require
lookup agreement after the actual backing fallback, together with matching
logical extent. Raw map reads and maximum indices may differ.
`UpdateMap/Lookup.lean` characterizes raw lookup-result agreement, including
failure and divergence; `ProgressiveList/Lookup.lean` proves it equivalent to
unchanged public `get` results. For example, an absent entry and `Some value`
agree exactly when the backing fallback returns `Some value`. The relation
still covers every machine index because pending entries take precedence over
backing bounds. An adapter proves exact map-read equality implies this weaker law.

`Clone/Maximum.lean` proves lookup agreement and matching maximum extent are
jointly necessary and sufficient for preserving the represented sequence.
`clone_success_represents_iff` and `clone_from_success_represents_iff` add actual
pending-map clone termination to characterize successful sequence-preserving
clones. The total clone proof and all dependent rebase contracts use the weaker
law; source representation supplies successor safety. Pending-update observers
retain their separate emptiness laws. At checkpoint `b93748b` (lookup criteria
`38c8b6d`), the focused and full builds pass (2,034 jobs), and the axiom/import
audit validates 5,099 declarations across 318 modules. New lookup and clone
criteria use only standard Lean axioms; no new axiom or admission was added.
These proof changes do not establish concrete map-model fidelity.

The shared `PackingLayout` assumption now requires only the actual factor
query and the routing power-of-two law. Its packing-depth result is derived
from those facts, with the word bound supplied by the represented factor and
no use of the `size_of` fallback axiom. Both layout constructors drop the
separate depth proof argument; their callers are updated. The public operation
specifications inherit this premise reduction through the shared invariant.

The model dependency inventory finds 151 local declarations across seven model
modules under the 42 available roots. None of those definition closures
references the older `List::intra_rebase` identity model, hash-map/hasher models,
or SmallVec models. This conservative inventory includes unused trait fields
and branches; it identifies trusted dependencies without proving runtime
reachability or source fidelity. The initial inventory narrowed external-model
comments without changing bodies. Subsequent review corrected tuple `ne` to
call element `ne` with Rust's short-circuit order, with six branch/result
lemmas and four native protocol regressions. Its optional hash-map dependency
is not reached by progressive updates: the source supplies `None`, and the
existing binary update proofs reduce that case directly. The full library and
both audit gates pass with the corrected model.

Constructor reflection now derives the finite actual input sequence from any
successful call, with exact stored contents, length, and default map. Iterator
constructor success is equivalent to finite input, occupied-layer capacity,
and successful default-map construction; vector entry points derive their
input trace internally. These equivalences do not assume finite input or a
successful default call in advance. Generic construction still initializes
the builder before reading the iterator, so its packing premise is retained.

The audit identified a real hypothesis limitation in successful SSZ decoding:
the earlier public contracts used a single encoding function for decoded
values. Per-occurrence payload contracts now cover distinct accepted encodings
of equal values in both formats and an accepted short final fixed chunk.
Empty input in the new contracts requires no element metadata or packing law.

The subsequent reflection proofs cover every successful public input without
assuming a payload encoding or parser trace. `SszItems.DecodesBytes` retains
the actual input branch, metadata and cursor initialization, and successful
per-occurrence payload calls. The exact stored values/count and actual default
map follow without codec or packing laws; indexed representation adds the
default map's empty behavior and packing layout only for nonempty input.
The complete success criterion also proves the occupied-layer capacity and
default-map termination conditions necessary, as well as sufficient.

The canonical fixed and variable content, representation, and total decoder
contracts now also omit metadata and packing assumptions for empty input.
Fixed positivity and reconstruction capacity are conditional on nonempty
contents. Both roundtrip contracts omit decoder metadata for empty contents;
the fixed roundtrip also omits decoder positivity and reconstruction capacity
there. Theorem names are retained with weaker premise types, and dependent
callers were updated. The canonical representation proofs reuse
`ProgressiveList.from_ssz_bytes_represents` from the general decoder trace work.

Fixed-encoder call equations now retain the actual reservation checks and
ordered element append calls, including each returned buffer, failure, or
divergence. They need no element codec law or byte bound. The exact fixed-byte
contracts use independent reservation and payload bounds, with no requirement
that payload lengths match declared width. Their append laws concern only
sequence positions and buffers containing the initial prefix and preceding
payloads. The owning encoder uses an empty initial prefix. The fixed roundtrip
uses the same restricted append law but retains width coherence for decoder
chunk boundaries and derives the encoder payload bound from it. These changes
pass the full build and axiom/import audit; they do not change external models.

Variable encoder and roundtrip append laws are now also restricted to actual
sequence positions and the preceding temporary payload. Element calls do not
receive the destination prefix or offset table. `VariableCalls.lean` proves
the exact fold of encoder append calls and borrowed continuations and lifts
it through public reservation and finalization, retaining failures/divergence
without codec or byte/offset laws. `LengthCalls.lean` proves the exact ordered
fold of element size calls and checked additions, followed by the public
offset-table arithmetic, without size laws or byte bounds. Overflow in the
fold stops later calls. Existing exact-byte and size-sum specifications remain
available for their successful fitting domains. The full build and axiom/import
audit pass after these changes, covering 5,012 declarations across 313 modules.

The revised goal is still incomplete. Borrowed-CoW obligations require faithful
extraction and models; existing counterexamples
and failed probes are recorded in
[UPSTREAM_BUGS.md](UPSTREAM_BUGS.md). The dependency-free
[reference-layout probe](reproducers/cow_regions/README.md) rules out the tested
lifetime separation, helper, and direct-copy approaches: eight enum readers
fail while four plain/nested/struct controls extract and validate without
axioms. This diagnostic adds no borrowed-method correctness claim.
The remaining theorem-hypothesis and model
fidelity audits are separate from this source inventory. No new extraction
result or general API completion is claimed here. Debug and Serde/context
implementations are excluded from the goal, and TreeHash is deferred for now.
Excluded or deferred implementations are not claimed proved by that decision.
