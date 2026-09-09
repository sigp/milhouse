# ProgressiveList source and proof inventory

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
| `get_mut` | `ProgressiveList.get_mut_total_spec`, `ProgressiveList.get_mut_represents_set_iff` |
| `get_cow` | `ProgressiveList.get_cow_represents_read`, `ProgressiveList.get_cow_into_mut_spec`, `ProgressiveList.cow_writeback_represents_set_iff`; borrowed handle methods remain pending below |
| `push` | `ProgressiveList.push_total_spec`, `ProgressiveList.push_represents_append_iff`, `ProgressiveList.len_after_push_iff_max_index`, `ProgressiveList.push_represents_append_iff_max_index` |
| `len` | `ProgressiveList.len_total_spec`, `ProgressiveList.len_success_iff` |
| `is_empty` | `ProgressiveList.is_empty_total_spec`, `ProgressiveList.is_empty_true_iff` |
| `has_pending_updates` | `ProgressiveList.has_pending_updates_spec` |
| `apply_updates` | `ProgressiveList.apply_updates_total_spec` |
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
| `Decode::from_ssz_bytes` | `ProgressiveList.from_ssz_bytes_trace`, `ProgressiveList.from_ssz_bytes_trace_spec`, and `ProgressiveList.from_ssz_bytes_success_iff`: every successful input determines its actual payload trace; success is equivalent to a complete trace, occupied-layer capacity, and a successful default-map call. Constructive payload contracts remain `ProgressiveList.from_ssz_bytes_fixed_payloads_total_spec`, `ProgressiveList.from_ssz_bytes_fixed_final_payload_total_spec`, and `ProgressiveList.from_ssz_bytes_variable_payloads_total_spec`; empty, zero-width, malformed-offset, and prefix-error results are in the coverage record |
| `Serialize::serialize` | Out of scope. Historical Serde protocol findings: issue 20 |
| `Deserialize::deserialize` | Out of scope. Historical visitor/sequence and error-order findings: issues 20 and 22 |
| `Deserialize::deserialize_in_place` | Out of scope, including the inherited default. Historical source audit: issue 20 |
| `Arbitrary::arbitrary` | `ProgressiveList.arbitrary_total_spec`; feature `arbitrary` |
| `Arbitrary::arbitrary_take_rest` | `ProgressiveList.arbitrary_take_rest_total_spec`; actual default, not Vec's override |
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
| `Cow::into_mut` | `milhouse.cow.Cow.into_mut_spec`, `milhouse.cow.Cow.into_mut_missing_entry`, and the list's consuming write-back contract |
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
validate `mem::take`, `usize::div_ceil`, `u128::saturating_mul`, and `u128::checked_pow` against their
actual extracted standard-library bodies, including arbitrary Default results,
zero divisors, saturation on overflow, and checked-power termination/overflow.
Their shared audit and all seven native tests pass. Checked multiplication
remains an Aeneas foundation primitive; three
other numeric helpers retain missing intrinsic templates (UPSTREAM_BUGS issue
24). No production model or public-operation specification changed.

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
