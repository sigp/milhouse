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
| `new` | `ProgressiveList.new_total_spec`, `ProgressiveList.new_success_iff` |
| `try_from_iter` | `ProgressiveList.try_from_iter_total_spec`, `ProgressiveList.try_from_iter_trace`, `ProgressiveList.try_from_iter_trace_spec`, `ProgressiveList.try_from_iter_success_iff` |
| `get` | `ProgressiveList.get_of_pending_update`, `ProgressiveList.get_of_backing`, `ProgressiveList.represents_of_dense_backing`; constructors and mutations establish/preserve indexed representation |
| `get_mut` | `ProgressiveList.get_mut_total_spec` |
| `get_cow` | `ProgressiveList.get_cow_represents_read`, `ProgressiveList.get_cow_into_mut_spec`; borrowed handle methods remain pending below |
| `push` | `ProgressiveList.push_total_spec` |
| `len` | `ProgressiveList.len_total_spec`, `ProgressiveList.len_success_iff` |
| `is_empty` | `ProgressiveList.is_empty_total_spec`, `ProgressiveList.is_empty_true_iff` |
| `has_pending_updates` | `ProgressiveList.has_pending_updates_spec` |
| `apply_updates` | `ProgressiveList.apply_updates_total_spec` |
| `iter` | `ProgressiveList.iter_spec` |
| `iter_from` | `ProgressiveList.iter_from_spec`, `ProgressiveList.iter_from_error_iff` |
| `iter_cow` | `ProgressiveList.iter_cow_spec`; constructor only, stepping pending |
| `iter_cow_from` | `ProgressiveList.iter_cow_from_spec`, `ProgressiveList.iter_cow_from_error_iff`; stepping pending |
| `to_vec` | `ProgressiveList.to_vec_total_spec`, `ProgressiveList.to_vec_mapM` |
| `pop_front` | `ProgressiveList.pop_front_nonzero_clones_total_spec`, `ProgressiveList.pop_front_total_spec`, `ProgressiveList.pop_front_success_iff`, `ProgressiveList.pop_front_out_of_bounds` |
| `rebase` | `ProgressiveList.rebase_total_spec` |
| `rebase_on` | `ProgressiveList.rebase_on_total_spec` |

## List trait methods

The pinned dependency sources were checked for additional methods:
`ethereum_ssz` 0.10.0 (`Encode`: five, `Decode`: three), `tree_hash` 0.12.0
(four), `serde` 1.0.217 (`Serialize`: one, `Deserialize`: two), `arbitrary`
1.4.1 (four), and `context_deserialize` 0.2.0 (one). In particular, the context
trait has no additional in-place default. Ordinary Serde does.

| Trait method | Primary proof entry point, remaining obligation, or scope exclusion |
| --- | --- |
| `Default::default` | `ProgressiveList.default_eq_empty`, `ProgressiveList.default_represents` |
| `TryFrom<Vec<T>>::try_from` | `ProgressiveList.try_from_vec_total_spec`, `ProgressiveList.try_from_vec_success_iff` |
| `TryFromIter::try_from_iter` | `ProgressiveList.ssz_try_from_iter_total_spec`, `ProgressiveList.ssz_try_from_iter_success_iff` |
| `IntoIterator::into_iter` for `&ProgressiveList` | `ProgressiveList.into_iter_spec` |
| `Clone::clone` | `ProgressiveList.clone_total_spec`, `ProgressiveList.clone_success_iff` |
| `Clone::clone_from` | `ProgressiveList.clone_from_total_spec`; actual inherited method, made reachable by a concrete caller |
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

The separate [Option source comparison](reproducers/option_models/README.md)
now validates eleven local models against freshly extracted pinned
standard-library bodies and one additional `cloned` composition, all without
axioms. Direct `cloned` extraction remains unsupported at its higher-ranked
function item. This reduces a trusted-model review obligation; it does not
change API coverage or complete the borrowed CoW proofs.

The [core source comparisons](reproducers/core_models/README.md) additionally
validate `mem::take`, `usize::div_ceil`, and `u128::saturating_mul` against their
actual extracted standard-library bodies, including arbitrary Default results,
zero divisors, and saturation on overflow. Their shared audit and all five
native tests pass. Checked multiplication remains an Aeneas foundation
primitive. Checked power extracts but still needs a comparison proof; three
other numeric helpers retain missing intrinsic templates (UPSTREAM_BUGS issue
24). No production model or public-operation specification changed.

Clone and clone_from sequence contracts, and the rebase contracts that depend
on them, no longer require cloned maximum-index identity. Under unchanged map
reads, `Clone/Maximum.lean` proves the new metadata condition necessary and
sufficient: the returned maximum must give the same mathematical logical
length, using the backing length for `None` and `max (index + 1) backing_length`
for `Some index`. Source representation supplies successor safety. The
contracts assume no successful new list-length call. Reads remain constrained
at every machine index because public `get` queries the map before checking
backing bounds. The generalized contracts pass the full build and axiom/import
audit (5,015 declarations across 314 modules).

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
