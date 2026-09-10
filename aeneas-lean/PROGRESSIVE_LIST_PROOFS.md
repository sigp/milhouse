# ProgressiveList proof coverage

## Goal and scope

Prove high-level correctness lemmas for every public `ProgressiveList`
operation within the scope below, including its iterators and trait
implementations. Build on the existing `Tree`, `ProgressiveTree`, and
`ProgressiveList` lemmas, organize them in separate files as appropriate, and
commit each completed piece. Proven lemmas must be free of extraneous
assumptions. If a Rust bug creates messy or unintuitive Lean semantics, stop
and raise a warning as required by `AGENTS.md`. Any subsequently authorized
Rust changes should preserve intent and performance where possible.
Do not change Aeneas; raise its limitations for discussion and workarounds.

As requested on 2026-09-09, **Debug implementations and Serde implementations
are out of scope**. This excludes `Debug::fmt` for the list, both iterator
types, and supporting types; `Serialize`, `Deserialize`, the inherited
`Deserialize::deserialize_in_place`, and Serde-based context deserialization,
including their visitor/seed protocols. Their extraction and proof gaps do not
count as unfinished work for this goal.

The subsequent 2026-09-09 scope revision also **defers TreeHash implementations
for now**, including root computation, its pending-update rejection, parallel
hashing, and shared hash-cache writes. The Aeneas limitations are recorded in
UPSTREAM_BUGS issue 21. Existing TreeHash metadata and packing-rejection proofs
are retained; completing TreeHash is not required by the current goal.

SSZ `Encode`/`Decode` implementations, borrowed CoW operations and iterator
stepping, and the remaining assumption and model-fidelity audits for included
operations remain in scope. Cache invariants and explicit hash assumptions
needed by included operations such as rebasing also remain in scope. The goal
is still incomplete. These revisions supersede earlier checkpoint statements
that count Debug, Serde/context protocols, or TreeHash as required work.

Extraction or a wrapper equation alone does not establish an operation's full
correctness.
Unchecked internal helpers are proof dependencies, not substitutes for the
public-operation specifications below.

Proofs use the extracted Rust definitions. Assumptions about generic update
maps, element cloning/equality, codecs, and hashing must state the laws actually
needed by the operation. Representation invariants must be established by
constructors and preserved by mutations; do not assume the postcondition in a
lower-level hypothesis and count the wrapper as proved.

## Coverage

The [source and proof inventory](PROGRESSIVE_LIST_API_AUDIT.md) lists the 19
public inherent methods, direct and inherited trait entry points, returned
iterator/handle methods, and the corresponding theorem, unresolved obligation,
or explicit scope exclusion.
It is a source-coverage check, separate from hypothesis and model-fidelity audits.
The [model dependency audit](PROGRESSIVE_LIST_MODEL_AUDIT.md) inventories the
local external definitions referenced by the 42 available included entry
points and records the trusted boundaries that still need fidelity review.

| Operation | Required behavior | Current evidence / remaining work |
| --- | --- | --- |
| `empty`, `Default::default` | Empty contents, zero length, no pending updates | `Observers.lean` and `Contents.lean`: exact state, observer results, and representation of the empty sequence proved under the relevant empty-map laws; `Spine.lean` establishes the backing-spine invariant on successful construction without additional map laws. `Construction/Caches.lean` also proves all caches cleared after every successful empty/default construction, without map laws. |
| `new`, `try_from_iter`, `TryFrom<Vec<T>>`, `TryFromIter` | Preserve the input sequence and its length; establish representation invariants | `Construction/Overlay.lean` characterizes successful-result representation by the actual default map's overlay and logical extent. `OverlayConditions.lean` proves exact success-and-representation criteria for all four entry points: finite consumed input, occupied-layer `LengthFits`, and an actual default outcome with those overlay/extent laws. Iterator traces are recovered from execution; vector input supplies its own finite iterator. `Total.lean` derives execution, represented contents, `BackingValid`, and `SpineValid` from these laws; a separate emptiness law supplies the pending observer. Empty-map representation and total specifications remain adapters. `Trace.lean` recovers actual consumed/stored values, length, and default outcome without iterator, packing, or map-law premises; `Conditions.lean` retains the execution-only criteria. No builder or intermediate-call success is assumed. `Caches.lean` proves successful constructors initialize cleared caches without element, packing, map, or iterator laws, and `CacheTotal.lean` retains all four total cache contracts. Packing layout and remaining geometry/model-fidelity review remain explicit. |
| `len` | Length of the merged backing/pending view | `ProgressiveList/Length.lean` and `UpdateMap/Length.lean`: exact empty/nonempty-map arithmetic, backing lower bound, and successful evaluation below overflow proved. `len_total_spec` and `len_success_iff` derive the complete public result directly from the actual optional map maximum and characterize success by representability of a present maximum's successor, without indexed-read or representation laws; sequence agreement is established by constructor/mutation representation lemmas |
| `is_empty` | Equivalent to merged length zero | `IsEmpty.lean`: exact total answer from optional maximum metadata, necessary-and-sufficient successor-bound success, and a premise-free true-result characterization by zero backing length and an actual absent maximum. No indexed-read, representation, packing, backing, or successful length-subcall premise. The map's separate emptiness method is not used. `Observers.lean` retains the logical-length comparison lemma |
| `has_pending_updates` | Equivalent to a nonempty update map | `ProgressiveList.has_pending_updates_spec` proved |
| `get` | Merged sequence indexing, with pending values taking precedence; out-of-bounds returns none | `Tree/ProgressiveList.lean`: precedence and backing correspondence; `Construction/Representation.lean` connects dense bounded backing trees to sequence representation, including out-of-bounds reads. Representation is now established by successful `new`/`try_from_iter`, as well as empty/default, and preserved by the proved mutations under their respective map laws |
| `push` | Append one value, increase length by one, preserve earlier values; reject full lists unchanged | `Push/Total.lean`: complete actual append execution is proved from represented contents and laws for only the insertion at the nonfull logical end. Success represents the exact appended sequence; full-list rejection preserves the entire input, and both branches preserve the exact backing fields. No push/length success, clone, packing, or structural invariant is assumed. `Push/Capacity.lean` characterizes success and full rejection from optional maximum metadata without indexed reads or representation; `Push/State.lean` proves every returned Rust error is exactly full-list rejection unchanged. `len_after_push_iff_max_index` proves exact length growth requires precisely the appended index as the returned maximum. `Push/Lookup.lean` requires the new pending value at the appended key and agreement after the original backing fallback at other keys; exact raw map-read preservation is unnecessary. `push_represents_append_iff` in `Push/Maximum.lean` proves those lookup conditions and the maximum jointly necessary and sufficient without a read-law assumption. The existing read-back, sequence, and total contracts use the weaker lookup law, and the total proof uses the joint criterion. Earlier `Push.lean` and `Contents.lean` retain read-back, all-index preservation, exact length growth, and successful-execution append results; `Spine.lean` and `Backing.lean` preserve both backing-spine and dense/representable traversal invariants on success without extra map laws or capacity assumptions. `ProgressiveList/Caches.lean` preserves every backing-cache predicate on all returned states, including full-list rejection, without additional laws. |
| `get_mut` | Return the pending value or actual clone of the backing value; write-back changes only the chosen element; bounds and failure behavior | `Mutable/Fallback.lean`: exact pending-or-clone equation, including failures; read agreement with `get` needs clone identity only for the actual backing fallback. `Mutable/FallbackTotal.lean`: `get_mut_total_spec_of_fallback` proves successful access at every machine index, exact initial-value behavior, single-element replacement with unchanged logical length and backing fields, and out-of-bounds no-op. Clone termination and agreement of write-back lookups and maximum results are scoped to present elements; the missing-handle law is scoped to out-of-bounds access. All four map laws apply only to the actual fallback dictionary and environment. `Mutable/Conditions.lean` gives exact successful-value/acquisition criteria and proves fallback-clone termination necessary and sufficient for an actually present immutable read. The lookup law requires agreement after the actual backing fallback, even at the selected replacement; exact pending-map answers are unnecessary. `get_after_get_mut_eq_iff_lookup` and `get_mut_represents_set_iff` give exact read and sequence criteria, and the sequence proof uses the joint lookup/maximum criterion. The maximum law requires only the same logical extent at the original backing length. The write-back length equivalence characterizes exact result preservation, including failures and divergence, without bounds or representation premises; the successful-length corollary drops its separate index bound. No global clone law, clone identity, or structural backing premise is needed by the total replacement specification. `Spine.lean` and `Backing.lean` preserve the backing-spine and full traversal invariants for every write-back. `ProgressiveList/Caches.lean` preserves every backing-cache predicate through every returned mutable continuation without map or clone laws. |
| `get_cow` | Read without materializing an update; mutation writes only the chosen element and maintains map metadata | `CopyOnWrite/Contracts.lean` restricts map laws to the optional fallback selected by actual input lookups: `none` on a pending hit, otherwise the backing-read result. `Acquisition.lean` recovers that selection and the exact lifted map result without map laws. `Fallback.lean` proves handle-data read/failure correspondence, represented-index access, missing handles, and unchanged release. `Conditions.lean` proves the selected-fallback read and release laws necessary and sufficient for their public behaviors, without representation, clone, or termination assumptions. `Materialization.lean` characterizes acquisition followed by `Cow::into_mut` under the selected read law: a present read plus structural entry readiness and clone termination only for immutable returned handles. `FallbackConsuming.lean` proves complete execution and single-element replacement from these inputs and selected write-read/maximum-result laws, preserving logical length and backing fields. Entry-key equality, pending-handle classification, and clone identity are unnecessary. `get_cow_into_mut_writeback_spec` recovers the filled-entry footprint from actual successful calls. The older entry-location/pending-handle/absent-pending clone contracts remain adapters. `WriteBack.lean` retains exact read, length-result, and sequence criteria without a filled-footprint assumption. All sixteen original public theorem names/signatures remain available through `CopyOnWrite.lean` and `Consuming.lean`. `Cow/Consuming.lean` proves the actual consuming body and missing-entry rejection. Backing-spine, dense traversal, and cache predicates remain preserved. Rust `Deref`, borrowed `make_mut`, and CoW iterator stepping remain pending extraction obligations; handle-data observation and consuming mutation do not establish those methods. |
| `apply_updates` | Preserve merged contents and length; clear pending updates on success; restore state on error | `ApplyUpdates/Overlay.lean` characterizes representation by the actual rebuilt-value overlay and installed-map extent, without a separate clone-identity or empty-default law. The earlier overlay criterion uses backing/layout, numeric occupied-length laws at progressive layers, and reflection inside selected binary subtrees on nonempty application; the checked length supplies the numeric maximum bound. `Capacity.lean` retains occupied-capacity certification under those range conditions. `Backing.lean` now additionally proves preservation using numeric extent conditions on all reached progressive and binary ranges, without pending-value reflection. Its skipped-range variant derives every false-answer extent from agreement with the original values, leaving only positive numeric selection independent. Input representation supplies the dense update domain; actual checked length supplies the maximum bound. These backing theorems assume actual successful application and need no clone, range-termination, or default-map law. Existing reflection contracts are adapters. `Contents.lean` derives the rebuilt backing reads independently of default-map laws, and `Materialized.lean` identifies the exact stored sequence under selected clone preservation and `BulkSkippedValuesAgree`. This law allows pending entries beyond the reported maximum when they match unchanged backing in the selected skipped suffixes; the old global maximum-bound contracts are adapters. `Skipped.lean` proves this agreement necessary and sufficient for correct materialized reads and exact stored contents under the selected clone/range and backing laws. `MaterializedConditions.lean` characterizes successful materialization by occupied capacity, that agreement, and actual default construction, with default overlay/extent added for final representation. The no-op materializes exactly when the backing already stores the merged sequence. `Total.lean` derives execution from `BulkLayerGuardsPass` without range correctness, positive progressive selection, or skipped-value agreement. `GuardConditions.lean` gives exact execution criteria with reached-query termination, selected missing-update guards, and actual default construction on the necessary-and-sufficient side. Input representation/density, layout, occupied capacity, and selected clone termination remain upfront on the rebuilding branch; the no-op has no rebuilding conditions. The older `BulkLayerEnabled` and reflection contracts remain adapters. The new `_total_spec_of_guards` contracts combine these execution proofs with agreement in skipped binary/progressive ranges and suffixes, positive numeric selection, and retained/pending clone identity. They derive exact stored contents internally and establish representation, backing validity, and observer results without range-value reflection, using exact default-map overlay, extent, and emptiness laws. The earlier sufficient contracts remain adapters. `EnabledConditions.lean` gives four existence criteria for valid materialization, with or without final representation, on the rebuilding branch and across both branches. Capacity, positive selection, skipped-layer/suffix agreement, and an actual default outcome appear on the necessary-and-sufficient side; the representation variants add default overlay/extent. No successful update is assumed. `StartConditions.lean` additionally proves the start condition necessary and moves it into the exact criterion, using successful selected-layer execution recovered in `BulkUpdate/Visited.lean`; no start assumption is required upfront. The no-op branch carries no rebuilding start condition. `StoredCloneConditions.lean` additionally assumes only retained-slot and pending-value clone identity upfront, placing termination of all copied stored values in the exact criterion. `StoredClones.lean` derives this termination from actual successful execution, including stored copies later overwritten. The no-op carries no rebuilding clone requirement. `QueryConditions.lean` also moves termination of reached range queries into the exact criterion, with no query-termination law assumed upfront. The lower `QueryTermination.lean` modules derive it from actual success, and `LayerRangeScope.lean` proves complete coverage by progressive and selected binary query scopes. `Tree/BulkUpdate/RetainedClones.lean` proves clone identity necessary for correct binary contents, without range correctness, and equivalent under skipped-window value exclusion. `ProgressiveTree/BulkUpdate/SelectedSlots.lean` routes original/final mathematical slots through each selected binary result. The progressive and list `RetainedClones.lean` modules then derive selected clone identity from correct materialization. `CloneConditions.lean` removes upfront clone laws from four exact existence criteria: copied-storage termination and retained/pending identity are combined as `BulkCloneLaws` on the necessary-and-sufficient side. The remaining upfront laws are selected binary reflection, layout, and input invariants; final representation adds exact default overlay/extent. The no-op still has no rebuilding clone requirement. Binary `SkippedContents.lean` now characterizes correct binary contents by retained/pending clone identity and agreement with original slots in skipped windows, with no binary range-correctness law. Binary `Contents.lean` and extracted read-back accept that weaker agreement; previous exclusion contracts are adapters. Progressive/list `BinarySkipped.lean` derives the agreement from successful dense materialization. `Layer.lean` and progressive/list `Contents.lean` now lift the weaker binary agreement through all backing reads; `Materialized.lean` combines it with the numeric/skipped-agreement density contracts for exact stored contents. `SkippedConditions.lean` characterizes valid materialization by retained/pending identity, positive progressive selection, and all skipped-value agreements after actual success. `SelectionConditions.lean` provides four exact existence criteria, with or without final representation and across both branches, without range-value reflection or upfront clone/termination laws. Capacity, reached-query termination, `BulkCloneLaws`, actual missing-update guards, progressive selection, all skipped agreements, and actual default construction appear on the necessary-and-sufficient side; representation adds exact default extent and self-overlay. `BinarySelection.lean` now derives numeric binary selection from successful dense output. The new successful-result criterion in `SkippedConditions.lean` and all four `InputConditions.lean` existence criteria move that condition to the necessary-and-sufficient side as well. Layout and input representation/backing validity are the only upfront rebuilding preconditions; no separate clone, range, termination, guard-success, final occupied-capacity, or default-success law remains upfront. The no-op has no rebuilding conditions. Geometry/input and model-fidelity audits remain separate. `Conditions.lean` characterizes successful sequence preservation by the actual empty no-op or final occupied capacity plus a default outcome with those exact map laws, under the stated selected clone/range laws and skipped-value agreement. Pending emptiness supplies only its observer. Clone termination is confined to selected copies; identity is required only for retained stored slots and selected pending values. Range termination/correctness is scoped to reached queries for the actual maximum. Input representation supplies lookup termination and the dense update domain. `Capacity.lean` proves the execution-only occupied-layer `LengthFits` criterion without a semantic maximum law; backing preservation also no longer requires that law. `ApplyUpdates.lean` additionally characterizes equality of complete length results by actual default-map extent on the nonempty branch, without representation, geometry, clone, range, or successful-metadata premises; the no-op preserves even failed/diverging length results. Error restoration, successful state, and idempotence remain proved. `Caches.lean` preserves cache invariants on every returned state, including Rust errors, without representation, geometry, map, clone, or termination laws. `CacheTotal.lean` validates through the generalized total contract. Remaining clone/range/geometry minimality and model fidelity are separate obligations. |
| `iter`, `iter_from`, `IntoIterator` | Enumerate the merged sequence/suffix; reject invalid starting indices | `Iter/Construction.lean`: public `iter` enumerates the complete represented merged sequence; `iter_from` enumerates the requested suffix, accepts the end, and rejects oversized indices with the exact bounds error. Accepted-constructor premises are representation, packing layout, and dense backing layers with representable capacities; no additional map-read, iterator-output, or termination assumptions. `Iter/Bounds.lean` derives rejection from only actual optional maximum metadata and the oversized-index comparison, replacing its former representation premise; it also characterizes every returned bounds error. Binary and progressive traversal and the pending overlay are proved underneath. `Iter/Traits.lean` proves the same complete enumeration through the actual borrowed `IntoIterator` method, made reachable by `to_vec` |
| `ProgressiveListIter::next`, `size_hint`, `ExactSizeIterator::len` | Yield the next merged element; exact remaining length; exhaustion | `Iter/Next.lean`: live calls return the represented indexed value and preserve the constructed cursor; exhausted calls return unchanged `none`, including past-end indices. Pending replacements and extensions are covered. `Iter/Length.lean`: both size-hint bounds and exact length equal the represented suffix length; these observers require only agreement of the recorded and sequence lengths |
| `iter_cow`, `iter_cow_from`, `ProgressiveListIterCow::next_cow` | Enumerate mutable handles at successive indices; read-only and write-back behavior; exhaustion | `IterCow/Construction.lean`: the extracted constructors establish the exact backing suffix and merged pending overlay, retain the requested start and pending state, accept the logical end, and reject oversized starts with exact bounds errors and complete restoration. Accepted-constructor premises are representation, backing validity, and packing layout, with no additional map or cloning laws. `IterCow/Bounds.lean` proves exact agreement with read-only bounds errors and the constant original-state continuation. Its rejection theorem needs only optional maximum metadata and the numeric comparison, with no sequence reads, representation, backing, or packing premise. `IterCow/State.lean` proves exact unchanged release, error restoration, and backing preservation through arbitrary constructor continuations without representation or map-law premises. `next_cow` extraction/enumeration, handle dereferencing, and borrowed `make_mut` remain pending borrowing limitations (UPSTREAM_BUGS issues 9 and 16). Consuming handles through `into_mut` is proved separately; neither that result nor constructor invariants substitutes for iterator stepping. `ProgressiveList/Caches.lean` proves backing-cache preservation through every constructor continuation and returned error; this does not substitute for the still-unextracted iterator step. |
| `to_vec` | Return the cloned merged sequence in order | `ToVec/Loop.lean` and `Clones.lean`: actual collection equals ordered `List.mapM` of element cloning, including exact returned values, failures, and divergence, without clone laws. `Total.lean`: success is equivalent to successful termination of clones of represented values; the actual cloned output preserves length. Uses representation, backing density/representability, and packing layout; traversal and vector-push bounds are derived internally. `ToVec.lean` retains the original exact-contents contracts as specializations under identity cloning only for values in the sequence |
| `pop_front` | Remove the first `n` merged values, rebuilding the retained suffix; zero is a no-op and oversized removal preserves the list with a bounds error | `PopFront/OverlayTotal.lean` proves exact success-and-representation criteria using the removal bound, retained occupied-layer capacity, actual clone outcomes, and the actual default map's overlay/extent. Clone identity, absent map reads, and an absent maximum are not separately necessary. Zero removal omits clone/default laws; packing and traversal laws apply only to a nonzero in-bounds rebuild. `Overlay.lean` characterizes the successful result's representation, and the general `ProgressiveList/Overlay.lean` supplies the dense-backing equivalence. The total overlay contract derives actual execution, represented suffix, backing validity, exact cloned contents, recorded length, and installed map; its no-pending observer uses a separate emptiness law. Existing `Contents.lean` and `Total.lean` are adapters for identity clones and empty defaults. `Clones.lean` and `ClonesTotal.lean` retain the ordered nonidentity clone results. `Conditions.lean` characterizes success without map-content or clone-identity laws. `State.lean` proves unconditional zero removal, exact bounds errors, and unchanged returned error states. `Caches.lean` proves every successful nonzero rebuild has cleared caches without clone/map/shape laws. These results validate using only standard Lean axioms; remaining geometry and model-fidelity audits are separate. |
| `rebase`, `rebase_on` | Preserve the merged sequence and valid backing while rebasing sharing; retain metadata or return the actual map clone | `Rebase/SelectedTotal.lean` gives complete total contracts and exact success-plus-representation criteria: selected backing readiness and, for nonmutating rebasing, an actual map clone with fallback-aware reads and matching logical extent. `Lookup.lean` preserves complete in-place read results, including failure/divergence, and characterizes nonmutating read preservation without assuming representation or successful map reads. `Representation.lean` proves in-place representation equivalence and necessity/sufficiency of the actual cloned map's read/extent laws. Layout and geometry justify indexed traversal; `SelectedContents.lean` preserves materialized backing contents without those premises under selected semantic soundness. `SelectedCaches.lean` gives both public cache equivalences from actual success and the same semantic law, without geometry or map premises. Cache selection uses actual optional metadata, packing results, and machine clamps; immediate stops retain the original suffix, and base progressive caches are never imported. `Ready.lean` characterizes success, with packing queries conditional on entered node pairs. `State.lean` proves error-state retention and exact metadata/observer criteria; nonmutating pending-emptiness preservation requires its own map law. `Validity.lean` and `Cleared.lean` connect selected caches to reference-hash validity and remove collision assumptions for cleared originals. Existing `Contents.lean`, `Total.lean`, and cache contracts use the generalized proofs through invariant adapters. No internal successful execution is assumed by the total contracts. Semantic-premise minimality and model fidelity remain under review. |
| `Clone::clone` | Preserve logical contents and backing validity | `Clone/Total.lean` proves that actual list-clone success is equivalent to success of the pending-map clone, without representation, packing, or element laws. Its total specification preserves the represented sequence, valid backing, exact backing fields, and the actual cloned pending map under only termination, lookup agreement after the actual backing fallback, and matching logical extent for that map call. `Clone/Maximum.lean` proves lookup agreement and matching maximum extent jointly necessary and sufficient; raw read and maximum identity are unnecessary. `clone_success_represents_iff` characterizes successful sequence-preserving cloning by those raw outcomes and actual map-clone termination. No successful list-clone call is assumed. `Clone.lean`: the actual derived clone shares the backing tree and copies its recorded length; successful cloning preserves `BackingValid` without clone laws. Sequence representation is preserved when pending-map cloning preserves reads after the backing fallback and logical extent; the pending observer is preserved under its corresponding map law. No element-clone law or exact identity of the cloned map is assumed. `ProgressiveList/Caches.lean` preserves every backing-cache predicate without element or pending-map clone laws. |
| `Clone::clone_from` | Replace the destination with a clone of the source | `Clone/From.lean` connects the concrete Rust caller to the actual inherited trait default and characterizes its computation, including clone failure/divergence. Success is equivalent to success of the source pending-map clone. The total contract replaces the represented sequence, preserves source backing validity and exact backing fields, and returns the actual cloned source map. `clone_from_success_represents_iff` characterizes successful sequence replacement. All map laws concern only that source clone and require lookup agreement after the source backing fallback and matching logical extent, without raw read or maximum identity; the destination requires no invariant. Successful replacement preserves source cache predicates without map semantics, and the pending observer transfers under only the corresponding emptiness law. It calls the source map's `clone`, so no map `clone_from` law is needed. The proof-only root and actual generated dictionary are retained; no production implementation or external model is substituted. |
| `PartialEq` | Characterize equality under input-scoped element/map laws | `Equality/Correctness.lean`: actual extracted `eq` and `ne` terminate and characterize backing-tree structure, recorded length, and the explicit pending-map relation. Element `ne` laws cover only selected input pairs, respecting pointer shortcuts, packed-vector length rejection, and field/element short circuiting; the map law applies only to the actual pair when preceding comparisons succeed. Hash caches are ignored. Positive equality transfers the represented sequence and `BackingValid` under only input-scoped false-`ne` soundness and pending-map read/max agreement; it assumes no comparison termination, completeness, reflexivity, packing layout, literal map identity, or representation/backing validity of the other list. Direct structural representation transfer needs no backing-validity premise. `Equality/Pointer.lean` gives the exact shared-backing computation without element or map laws, including map failure/divergence. This is structural equality, so identical merged contents alone do not imply a true comparison |
| `Debug` for the list and both iterator types | Out of scope | Explicitly excluded from the proof goal, including `ProgressiveList`, `ProgressiveListIter`, and `ProgressiveListIterCow`. Historical formatter and lock-model findings are retained in UPSTREAM_BUGS issue 5. These implementations are not claimed proved. |
| `TreeHash` methods | Deferred; out of scope for now | `TreeHash/Metadata.lean` retains the proofs of List classification and unconditional rejection of unsupported packing methods. Root computation, pending-update rejection through the public root, length mix-in, parallel hashing, and shared hash-cache writes are deferred under the revised goal. Aeneas limitations are recorded in UPSTREAM_BUGS issue 21; the root implementation is not claimed proved. |
| `Encode` methods | SSZ encoding/encoded length of the merged sequence | `Encode/FixedLength.lean` and `Encode/Length.lean`: exact fixed-width multiplication and variable payload-size sum plus four-byte offsets. The fixed-width numeric contract requires only logical length, and the total contract derives that length internally from the returned map maximum, without indexed reads or sequence representation. Its success criterion proves successor representability and the final byte bound are necessary and sufficient; the successor check remains necessary at zero width. Variable-size accumulation derives intermediate bounds from the final byte bound. `Encode/LengthCalls.lean` additionally preserves actual size calls and checked arithmetic, including failure/divergence and overflow before later calls, without size laws or byte bounds. Fixed-size calculation needs no backing or traversal assumptions. `Encode/Fixed.lean`, `VariableLoop.lean`, and `Variable.lean`: actual `ssz_append` preserves the destination prefix and writes the exact represented merged payload, with the complete offset table for variable elements. `Encode/FixedCalls.lean` additionally gives the exact ordered fixed-element calls, including reservation checks, returned buffers, failure, and divergence without codec or byte-bound laws. Exact fixed-byte contracts use independent reservation and payload bounds, require no width coherence, and constrain append laws only on reached prefix buffers. `Encode/VariableCalls.lean` retains actual variable append calls, encoder states, continuation composition, reservation, and finalization without codec or byte/offset bounds. Variable append and roundtrip laws now concern only preceding temporary payload buffers. `Encode/Owning.lean` proves both exact `as_ssz_bytes` formats. `Encode/Metadata.lean` proves variable-list classification, four-byte fixed-section width, and the concrete owning wrapper. Representation and traversal invariants/layout are required only by methods that iterate. The remaining premises are the relevant element codec/size laws on consumed values, final output-size bounds, and 32-bit bounds only on offsets actually emitted. No clone law or assumed iterator output is needed. `Tree/Ssz` models and proves the pinned external encoder state, offset writes, payload accumulation, and finalization |
| `Decode` methods | Decode SSZ contents, including empty/invalid/zero-sized-element cases | `Decode/Overlay.lean` characterizes successful representation by the actual default map's overlay and logical extent. `OverlayTotal.lean` proves exact success and representation criteria from a complete input-bound payload trace, occupied-layer `LengthFits`, and an actual default outcome with those laws; its total contract derives execution, represented contents, valid backing, exact stored sequence/count, and installed map. Pending emptiness is a separate observer law. `Trace.lean` and `PublicTrace.lean` recover the actual per-occurrence payload trace and stored state without supplied parser, canonical-encoding, codec, packing, or map laws; supplied complete traces agree with execution. `Conditions.lean` retains the execution-only criterion. `FixedTotal.lean` and `VariableTotal.lean` provide canonical-byte total contracts with the exact map conditions, and the existing empty-map contracts are adapters. Empty input bypasses element metadata and packing; fixed positivity/capacity remain conditional on nonempty contents. `PayloadFixed.lean` and `PayloadVariable.lean` retain constructive per-occurrence contracts, including distinct encodings of equal values, empty variable payloads, and an accepted short final fixed chunk. `FixedRoundtrip.lean` and `VariableRoundtrip.lean` compose actual owning encoding and public decoding, preserving the merged sequence and every indexed read while clearing pending updates. `Decode/Success.lean` proves streaming construction terminates with the exact decoded prefix and retained error. `ProgressiveTree/LengthFits.lean` and `Builder/PushLength.lean` derive every rollover bound from representability of the final sequence; fixed decoding retains this condition for general element widths, while the variable offset table supplies it internally. `Backing.lean` proves backing validity after any successful public decode without element-codec or parser laws. The cursor modules derive parsing from canonical bytes, including 32-bit bounds only on emitted offsets. `Decode/Entry.lean` covers metadata, empty input, zero fixed width, and short variable prefixes; `Ssz/VariableInit.lean` covers first-offset bounds/alignment/zero errors in the actual check order. `Decode/ErrorMessages.lean` proves exact builder-error text; `Ssz/ReadOffset.lean` proves four-byte reads and canonical offset roundtrips. Streaming bodies extract with the real error enum and local external models (UPSTREAM_BUGS issue 19); differential release tests cover error order and partial-builder finalization. `Decode/InitialErrors.lean` derives public first-offset bounds, alignment, and zero errors from raw offset bytes without packing, map, or element laws. `Decode/FixedErrors.lean` returns the first invalid element error after an arbitrary successful prefix, covering short final chunks and unconstrained bytes after a full-width invalid element. `Decode/VariableErrors.lean` derives second-offset fixed-section/bounds errors and third-offset decreasing errors directly from bytes, with exact element/error order. `Decode/ErrorResult.lean` propagates arbitrary cursor error traces through actual successful prefix finalization; `Ssz/DecodedLength.lean` derives variable prefix capacity from the table even for malformed input. `Ssz/VariablePrefix.lean`, `VariablePrefixErrors.lean`, and `VariableElementErrors.lean` derive every prefix step from raw table and payload bytes. `Decode/VariablePrefixErrors.lean` and `VariableElementErrors.lean` return the exact malformed-offset or element error after any successful prefix, including empty final payloads. `Decode/PayloadErrors.lean` generalizes both formats to per-entry payload bytes: equal values may have distinct accepted encodings, with no canonical-encoding assumption. `Ssz/PayloadTrace.lean` erases proof-level byte annotations to recover the exact original decoder trace. All public prefix-error results establish actual parser and builder behavior internally; later bytes and decoder calls are unconstrained. `Decode/Caches.lean` proves every successful public decoder initializes cleared caches, also covering partial lists finalized after streaming element errors, without parser, packing, map, element, or finiteness laws. |
| `Serialize`, `Deserialize`, `Deserialize::deserialize_in_place` | Out of scope | Explicitly excluded from the proof goal, including the inherited in-place default and visitor/sequence protocols. Historical extraction and source-audit findings are retained in UPSTREAM_BUGS issues 20 and 22. These implementations are not claimed proved. |
| Context deserialization feature | Out of scope | Serde-based `ContextDeserialize` and its contextual visitor/seed protocol are explicitly excluded from the proof goal. Historical extraction findings are retained in UPSTREAM_BUGS issue 22. This implementation is not claimed proved. |
| `Arbitrary` feature | Preserve actual generated values and consumed-input state; establish valid backing and length | `Arbitrary/Overlay.lean` characterizes representation by the actual default map's overlay and logical extent. `Conditions.lean` proves exact success and success-plus-representation criteria using actual finite control/element traces, occupied-layer `LengthFits`, and default-map outcomes, without a supplied trace or successful subcall. `Traits.lean` gives the same criteria for the actual owning-input default, recovering its discarded final input. `Generated.lean` derives the actual trace and complete representation/backing/spine contract under the exact map conditions. `Total.lean` and `Traits.lean` derive successful generation, representation, and valid backing/spine; pending emptiness is separate and supplies only its observer. Existing empty-map contracts are adapters. `Behavior.lean` retains exact stored sequence/length/default state and backing validity; first element errors retain their consumed input, and constructor errors map to `IncorrectFormat`. Both size-hint methods are proved at every depth. All four trait entry points are extracted. `Tree/Arbitrary/Models.lean`, `Generation.lean`, and `Reflection.lean` model and prove external Vec collection, including stopping-byte consumption, first-error state, and custom input replacement; vector success is equivalent to a finite trace. No element-consumption law or intermediate milhouse success is assumed. `Caches.lean` proves both generators initialize cleared caches on every successful result without generator, packing, or map laws. External-model fidelity and remaining geometry/premise review remain separate obligations. |

## Existing foundations

- `UpdateMap/MaxMap/Mutable.lean` proves the actual extracted `get_mut_with`
  result and complete continuation. The wrapper preserves the inner initial
  value and success/failure/divergence behavior. Present loans record the
  selected key; missing loans preserve cached metadata. Exact lookup frames
  and whole-map restoration transfer from the actual inner loan without laws
  about unrelated callbacks, inner maximum queries, cloning, or index bounds.
  The two CoW wrapper methods now extract and compile too, but their own
  correctness contracts and concrete dictionary composition remain unfinished.
- `UpdateMap/MaxMap/Operations.lean` proves the actual extracted wrapper's
  default construction, lookup, cardinality, cached maximum, and insertion
  behavior over an arbitrary inner `UpdateMap`. Insertion propagates the inner
  result and records the key; the exact maximum update needs no inner maximum
  law, cache invariant, cloning law, or index/successor bound.
  `Maximum.lean` defines cache validity by bounding successful present reads
  and attaining a present maximum. It characterizes valid default construction
  by the actual inner outcome and proves insertion preserves validity from
  the inner insertion's lookup frame. These seventeen public lemmas prove
  wrapper behavior; the concrete inner dictionary and borrowed map operations
  remain separate obligations.
- The independent [VecMap source suite](reproducers/vec_map_models/README.md)
  proves exact construction/observer/mutable-lookup equations from pinned
  source, including the actual Option borrow helpers. Six derived contracts
  establish the occupancy-count invariant, give semantic cardinality and
  emptiness, and preserve occupancy through every mutable continuation.
  These thirteen proofs retain vector/scalar/reference foundations and live
  outside `Tree`. Concrete insertion, range/max operations, entry footprints,
  and `UpdateMap`/`MaxMap` composition remain separate fidelity obligations;
  insertion's tested iterator-signature failure is recorded in UPSTREAM_BUGS 28.
- Binary `Selection.lean` derives positive numeric selection from actual
  rebuilding and dense output, using layout and prefix alignment without input
  invariants, clone/range laws, offset alignment, or capacity assumptions.
  Progressive `BinarySelection.lean` recovers the actual selected binary result
  and its clipped dense length, then lifts selection necessity through the
  public wrapper. The list module derives selection without input representation
  or backing validity. `SkippedConditions.lean` and the four existence criteria
  in `InputConditions.lean` now place all clone, range, guard, numeric selection,
  skipped-value, final occupied-capacity, and default-success conditions on the
  necessary-and-sufficient side. Only layout and input representation/backing
  validity remain upfront on rebuilding; final representation adds exact default
  extent and self-overlay in the criterion. The no-op has no rebuilding laws.
  This checkpoint adds 11 public lemmas using standard Lean axioms. Binary
  selection necessity is complete for these contracts; remaining geometry/input,
  borrowed CoW, and model-fidelity review is separate.
- Selected-layer `Layer.lean`, progressive/list `Contents.lean`, and list
  `Materialized.lean` now accept agreement with original slots in skipped binary
  ranges, without range-value exclusion or reflection. This joins the earlier
  progressive-layer/suffix agreements and retained/pending clone identity.
  Complete nonempty/all-branch `_total_spec_of_guards` contracts derive execution,
  representation, backing validity, and the pending observer from these weaker
  laws and the actual default map's extent, overlay, and emptiness conditions.
  `SkippedConditions.lean` proves the clone/agreement conditions necessary and
  sufficient for valid materialization after successful application.
  `SelectionConditions.lean` gives four exact valid-materialization existence
  criteria without upfront clone or termination laws or range-value reflection.
  The subsequent `InputConditions.lean` criteria above derive positive numeric
  binary selection too, removing that remaining upfront range condition. The
  old sufficient contracts retain their signatures as adapters.
  This checkpoint adds 19 public lemmas using standard Lean axioms.
- Binary `Density.lean` now preserves density using numeric effects of reached
  range answers, without pending-value reflection. Skipped intervals retain
  their occupied lengths; selected intervals start inside the final prefix.
  `SkippedExtents.lean` derives the false-answer law from matching original
  dense slots and the local extension conditions. The progressive
  `BinarySkippedExtents.lean` lifts this result using pure selected-slot routing,
  without input capacity or a rebuilding result. Progressive density and
  `ApplyUpdates/Backing.lean` now accept either numeric conditions on all reached
  ranges or agreement in skipped ranges plus positive numeric selection. No
  clone or default-map law is needed for backing validity. Previous reflection
  contracts retain their signatures as adapters. This checkpoint adds 14 public
  lemmas using standard Lean axioms. These weaker density conditions now
  support the materialization criteria above; binary numeric selection is now
  also proved necessary and included in their exact conditions.
- `Tree/BulkUpdate/Guards.lean` describes the actual missing-update guards,
  independently of pending-witness reflection or an assumed update result.
  `GuardsNecessary.lean` derives them from successful rebuilding using layout,
  input shape, and prefix alignment. Binary and progressive `Success.lean`
  now prove sufficient and exact execution criteria using guards without range
  correctness; the earlier enabled/reflection contracts remain adapters.
  The progressive/list guard scopes lift necessity to selected binary calls.
  `ApplyUpdates/GuardConditions.lean` characterizes public execution by reached
  query termination, selected guards, and actual default construction, under
  the remaining input, occupied-capacity, and clone-termination laws on the
  rebuilding branch. The no-op has no rebuilding conditions. These execution
  contracts now support the materialization criteria above. This checkpoint
  adds 19 public lemmas using standard Lean axioms.
- `Tree/BulkUpdate/Skipped.lean` permits a pending value in a range
  answered false when it already matches the original slot. Its input scope
  uses the existing queried-range relation, with bounds and child-routing
  lemmas; no update result is part of the agreement condition.
  `Contents.lean` now proves shape/capacity/content preservation and extracted
  read-back under this weaker agreement law. Existing exclusion contracts
  retain their signatures as adapters. `SkippedSlots.lean` proves every skipped
  slot preserved by actual successful rebuilding with layout and prefix alignment
  only, without shape, density, capacity, offset alignment, range, clone, or
  termination laws. `SkippedContents.lean` makes binary contents equivalent to
  retained/pending clone identity plus skipped-value agreement, with no range
  correctness assumed in either direction. The selected progressive content
  bridge and the progressive/list `BinarySkipped.lean` modules lift agreement
  necessity to dense, exact list materialization. The weaker content, density,
  and execution contracts are now combined in the public materialization
  criteria above without range-value reflection. Positive numeric binary
  selection is also necessary and belongs to the exact criterion.
  Scope/routing is `79282b8`, generalized contents `7a2235e`, binary
  equivalence/selected bridge `8d17355`, and progressive/list necessity
  `30c17f3`. All 19 new public lemmas use standard Lean axioms. Remaining
  range/geometry minimality, borrowed CoW, and model-fidelity work stays open.
- `ProgressiveTree/BulkUpdate/SelectedSlots.lean` identifies each selected
  layer's unclamped mathematical position and routes the original and final
  progressive slots through its input and actual rebuilt binary result. Layout
  and actual selection/execution suffice, without shape, density, range,
  clone, or termination laws. `RetainedClones.lean` lifts binary clone-identity
  necessity to progressive rebuilding from input shape and correct mathematical
  suffix slots. `ApplyUpdates/RetainedClones.lean` derives that slot relation
  from input representation/backing validity and dense, exactly materialized
  output; no output capacity, range, maximum, default, clone, or termination
  law is assumed. `ApplyUpdates/CloneConditions.lean` removes upfront clone
  laws from four exact valid-materialization existence criteria, with or without
  final representation and across both branches. `BulkCloneLaws` on the
  necessary-and-sufficient side combines copied-storage termination with
  retained/pending identity, allowing overwritten copies to change value.
  Query termination, start, capacity, selection, skipped-value agreement, and
  actual default conditions remain there. Selected binary reflection, layout,
  and input invariants remain upfront; the no-op needs no rebuilding laws.
  Selected-slot routing is `b1246e7`, progressive necessity `18b4833`, list
  necessity `5e01cf9`, and public criteria `6f2915e`. All ten new public lemmas
  use standard Lean axioms. Binary range and geometry minimality, borrowed CoW,
  and model fidelity remain unfinished.
- `Vec/Clone.lean` recovers actual optional slot clones from a successful
  vector copy and characterizes slot preservation by clone identity.
  `PackedLeaf/BulkUpdate.lean` tracks the actual cloned value through the
  scan and complete update, without a clone-identity or termination law;
  existing identity-based contracts are adapters. `BulkUpdateIdentity.lean`
  proves packed-window contents correct exactly when retained stored slots
  and pending values clone identically. Overwritten stored copies require no
  identity law. `Tree/BulkUpdate/CloneIdentity.lean` restricts correct node
  contents to each child and handles unpacked and packed terminals.
  `RetainedClones.lean` lifts necessity through selected children and zero
  expansion: successful rebuilding with correct binary contents forces
  `BulkRetainedCloneOn` identity, using layout, input shape, and alignment,
  without range correctness, density, capacity, clone, or termination laws.
  With exclusion of pending values from skipped binary windows, the existing
  sufficiency theorem gives an equivalence. Actual clone tracking is
  `1bc9b38`, packed identity `e6ea416`, terminal/routing lemmas `ba2a10c`, and
  binary necessity/equivalence `c3b836b`. All 13 new public lemmas use only
  standard Lean axioms. The subsequent progressive/list result above removes
  the retained/pending clone assumption from the newest public criteria.
- `Tree/BulkUpdate/QueryTermination.lean` derives termination of every
  scoped binary range query from actual success, using layout and prefix
  alignment without shape, density, capacity, clone, lookup, or range correctness.
  `ProgressiveTree/BulkUpdate/LayerRangeScope.lean` proves that the full scope is
  exactly progressive queries plus selected binary queries. The progressive
  `QueryTermination.lean` proves layer-query termination without metadata laws,
  then covers the full scope with layout only. The public list lemma lifts this
  to nonempty `apply_updates`. `ApplyUpdates/QueryConditions.lean` puts query
  termination on the necessary-and-sufficient side of four valid-materialization
  existence criteria, alongside stored-clone termination, start, capacity,
  selection, agreement, and actual default construction. Retained/pending
  identity, selected binary reflection, layout, and input invariants remain
  upfront. The no-op has no rebuilding query or clone condition. All 11 new
  lemmas and the newly public geometry-step helper use standard Lean axioms.
  Binary necessity/helper is `b6b4338`, exact scope `0095ccd`, progressive/list
  necessity `ceb502f`, and public criteria `09b6d34`. Remaining identity,
  binary range, geometry, and model-fidelity obligations are not discharged.
- `Tree/BulkUpdate/StoredCloneScope.lean` separates copied-storage laws
  from pending-value laws and proves that `BulkCloneLaws` is exactly stored
  clone termination plus identity on retained slots and selected pending values.
  `PackedLeaf/BulkUpdateClones.lean` derives termination of every initial stored
  clone from any returned packed-update result, even a Rust error, without
  metadata or input invariants. `Tree/BulkUpdate/StoredClones.lean` derives the
  selected storage law from successful binary rebuilding with layout and prefix
  alignment only; it needs no shape, density, range, clone, or termination law.
  Progressive and list `StoredClones.lean` lift this through actual selected
  calls, needing only layout on nonempty application. The four criteria in
  `ApplyUpdates/StoredCloneConditions.lean` retain only surviving-slot and
  pending-value identity upfront. Stored-clone termination joins start,
  capacity, positive selection, skipped-value agreement, and actual default
  construction on the necessary-and-sufficient side. The representation
  variants also require exact default extent and self-overlay; the no-op has
  no rebuilding clone requirement. All 13 new named lemmas use standard Lean
  axioms. Scope/packed necessity is `5934163`, binary necessity `c9ca4f3`,
  progressive/list necessity `5595942`, and public criteria `d3dbb3c`.
  Remaining identity, range, query-termination, geometry, and model-fidelity
  obligations are not discharged by these results.
- `Tree/BulkUpdate/ActivationNecessary.lean` proves the binary start
  condition necessary for success, using only positive range witnesses,
  alignment, packing layout, and packed-leaf metadata compatibility. It needs
  no false-answer, clone, density, capacity, or termination law. The stronger
  node-step lemma retains the necessary positive child answer. The progressive
  `BulkUpdate/Visited.lean` recovers an actual successful binary call at each
  selected layer without external or input-invariant laws, and separately
  inherits the layer's shape from the input. The progressive and list activation
  lemmas then derive selected start conditions from success. Binary and
  progressive `Success.lean` give exact success equivalences under the remaining
  execution and input laws. `ApplyUpdates/StartConditions.lean` removes upfront
  start assumptions from four valid-materialization existence criteria, with
  or without final representation, on the rebuilding branch and across both
  branches. Start conditions join occupied capacity, positive selection,
  skipped-layer/suffix agreement, and an actual default outcome on the
  necessary-and-sufficient side. Final representation additionally requires
  exact default extent and self-overlay. The no-op needs valid backing already
  storing the contents; its representation variant also uses input
  representation. All 16 new named lemmas use standard Lean axioms or none.
  Node selection is `3d2a8b4`, binary necessity/equivalence `85703b8`, selected
  execution/shape `effb200`, progressive/list necessity `ffe7dc6`, and public
  existence criteria `0f0b606`. Remaining binary range, clone, and geometry
  minimality and model fidelity are not established by these results.
- `Tree/BulkUpdate/Activation.lean` defines input-only start conditions:
  unpacked leaves and internal nodes require a pending value in their binary
  window, while packed terminals can scan without one. The progressive
  `BulkUpdate/Activation.lean` scopes this condition to selected layers and
  derives it from the previous range-reflection law. The binary and progressive
  success proofs now use these weaker conditions. `ApplyUpdates/Total.lean`
  derives raw execution without positive progressive selection or skipped-value
  agreement; its new total contracts add those conditions for valid backing and
  preserved contents, plus exact default overlay/extent for representation and
  default emptiness for its observer. `ApplyUpdates/EnabledConditions.lean`
  gives four existence equivalences for valid materialization, with or without
  final representation, on the rebuilding branch and across both branches.
  They require no supplied successful update or default construction: occupied
  capacity, positive selection, skipped-layer/suffix agreement, and an actual
  default outcome appear on the necessary-and-sufficient side. The combined
  representation criteria additionally require that default's exact extent and
  overlay. The no-op must already have valid backing storing the contents.
  The remaining selected clone, query-termination, binary-reflection, layout,
  and input laws are explicit; their full necessity/minimality is not claimed.
  All 18 new named lemmas use standard Lean axioms or none. Binary activation is
  `6650b5d`, progressive scope `9b286fc`, progressive execution `13cac37`, public
  execution `2915fca`, total correctness `56bb004`, and existence criteria
  `4063863`/`ded30f2`. Existing contracts remain available as adapters.
- `ProgressiveTree/BulkUpdate/LayerSkippedExtents.lean` derives false-answer
  occupied-length equality from skipped-layer agreement, input density, and
  extension completeness. It uses `LayerSkippedReads.lean` to route original
  backing reads through the recorded input layers; no rebuilding result is
  assumed by this implication. `RangeSelectsInsideAt` retains only the positive
  range condition. Density, public backing preservation, and materialization
  have variants using agreement and positive selection without a separate
  false-answer extent law. `Tree/BulkUpdate/Nonempty.lean` proves that any
  successful binary rebuild has nonzero output shape, with no packing,
  alignment, map, or clone law. `LayerSelection.lean` combines this fact with
  output density to prove positive progressive selection necessary.
  `apply_updates_nonempty_backing_valid_contents_iff` and
  `apply_updates_backing_valid_contents_iff` now characterize valid stored
  materialization by positive selection and agreement in skipped layers and
  suffixes, assuming only the remaining selected binary/clone laws and input
  invariants. Neither progressive selection nor agreement is assumed upfront.
  The all-branch criterion needs input representation only when rebuilding;
  the no-op must already store the contents. These are criteria for actual
  successful execution, not termination proofs. All 18 new named lemmas use
  standard Lean axioms or none. Input routing is `1474367`, derived extents
  `42d7ca1`, density `6fb973a`, public sufficiency `2226423`, binary nonzero
  output `0f38573`, necessary selection `16b9b2c`, and final criteria `10447d8`.
  At this checkpoint, binary range/clone/geometry minimality and weaker
  termination/total contracts remained open; the newer results above address
  the termination/total contracts. Final representation may also permit
  default-overlay repair.
- `ProgressiveTree/BulkUpdate/LayerSkipped.lean` records input layers skipped
  by actual false range answers. `BulkLayerSkippedValuesAgree` permits present
  pending values that match unchanged reads inside the layer and final prefix.
  Its scope follows the actual range/maximum guards without assuming an update
  result. `LayerSkippedBounds.lean` derives the empty-zero bound from agreement
  and extension completeness. The progressive and list contents proofs now
  require exclusion only on selected binary queries; existing contracts are
  adapters. `CapacitySuccess.lean` derives packing-factor success and monotone
  capacities from actual successful calculations. `LayerSkippedReads.lean`
  then proves complete read preservation in skipped layers without packing,
  shape, clone, range-correctness, or lookup-termination laws. At list level,
  `apply_updates_nonempty_backing_reads_iff_layer_agreement` characterizes
  correct materialized reads by agreement in both false-range-skipped layers
  and maximum-skipped suffixes. With numeric layer extents and selected binary
  reflection, `apply_updates_nonempty_backing_contents_iff_layer_agreement`
  characterizes exact stored contents the same way. Neither criterion assumes
  agreement upfront or constrains the installed default map. All 22 new named
  lemmas use only standard Lean axioms. Scope/bounds are `2f3e7bc`/`f3248ed`,
  contents `b53be68`/`bacc216`, successful-capacity geometry `f146b17`, necessary
  layer agreement `84224a8`, read equivalence `5481b38`, and materialization
  `5a9398e`. The later valid-materialization criteria above discharge the
  independent layer-extent premises. Termination/total contracts and binary/
  clone/geometry minimality still require review. Agreement is necessary for materialization; representation alone may
  still be repaired by the installed default overlay.
- `UpdateMap/RangeExtent.lean` defines `RangePreservesExtentAt`: a false
  answer preserves the interval's occupied length, and a true answer starts
  inside the final prefix. `ProgressiveTree/BulkUpdate/LayerRangeScope.lean`
  separates these conditions on reached progressive layers from reflection
  inside selected binary subtrees. Both scopes follow actual geometry and
  range/maximum guards, without assuming a rebuilding result. `Range.lean`
  derives the empty-zero bound without pending-value exclusion, including
  saturated endpoints. `Density.lean` proves density under these separate laws.
  The public `apply_updates` backing-preservation, occupied-capacity, and two
  actual-rebuilt-value representation lemmas have corresponding
  `_of_range_extents` generalizations. The existing reflection contracts are
  adapters; the represented input supplies their conversion. All 21 new
  named lemmas use only standard Lean axioms. Scope and conversion are
  `78cacde`, empty-layer bounds `01415b8`, density `2416785`, and public
  integration `3780516`. The later layer-agreement refinement also weakens
  content/materialization; termination contracts retain stronger range laws.
  Necessity of the numeric layer conditions,
  binary range/clone/geometry minimality, and source fidelity remain open.
- `ProgressiveTree/BulkUpdate/SkippedReads.lean` proves that every actual
  successful update preserves the complete read result of a selected skipped
  suffix, including failure/divergence. The maximum guards route each ancestor
  without packing, shape, clone, or range-correctness laws. Consequently,
  `ApplyUpdates/Skipped.lean` derives skipped-value agreement from correct
  materialized pending reads without input representation or default-map laws.
  Under the existing selected clone/range and backing laws, agreement is
  equivalent to correct backing reads and exact stored contents.
  `MaterializedConditions.lean` characterizes successful materialization by
  occupied final capacity, skipped-value agreement, and actual default
  construction. The combined materialization/representation criterion adds
  exact default overlay and extent. These conditions are conclusions of the
  forward direction, rather than premises. The public no-op branch requires
  the backing already to store the merged sequence; all rebuilding laws are
  conditional on nonempty application. `Conditions.lean` reuses the combined
  criterion. All 10 new named lemmas use only standard Lean axioms. Suffix
  reads are `19dee5c`, materialization equivalence `034d26b`, and success
  criteria `dda608d`. Necessity here concerns materialization; a default overlay
  can compensate for different stored values in the separate representation
  criterion. Selected clone/range and geometry minimality remain open.
- `ProgressiveTree/BulkUpdate/Skipped.lean` defines skipped input suffixes
  from the actual geometry, range, and maximum guards, without assuming an
  update result. `BulkSkippedValuesAgree` requires only present pending values
  inside the new logical prefix to agree with those unchanged suffix reads;
  redundant matching entries beyond the reported maximum are permitted.
  `Contents.lean` proves recursive and public bulk contents from this law and
  a numeric extension bound. The public list's checked length supplies that
  bound internally. `ApplyUpdates/Contents.lean` and `Materialized.lean`
  derive backing reads, representation, and exact stored contents under the
  weaker law. `Total.lean` and `Conditions.lean` carry it through complete
  public execution and success/representation criteria with exact default-map
  overlay and extent. All work laws remain conditional on nonempty application.
  The old semantic-maximum contracts are adapters. All 15 new named lemmas
  use only standard Lean axioms. Scope is `25f577f`, bulk contents `ad51425`,
  list contents `592280c`, and total/criterion integration `10c8634`.
  This removes the global maximum bound from the generalized contracts.
  Skipped-value necessity for materialization is proved above; selected clone/
  range minimality, geometry minimality, and source fidelity remain separate
  obligations.
- `ProgressiveTree/BulkUpdate/Density.lean` derives density from a numeric
  extension bound, without requiring every pending value to lie below the
  reported maximum. `UpdateMap/Domain.lean` derives this bound from the old
  semantic maximum law for compatibility. For `apply_updates`, the actual
  checked length calculation already supplies the bound. Consequently,
  `apply_updates_preserves_backing`, both occupied-capacity criteria in
  `Capacity.lean`, and both actual-rebuilt-value representation criteria in
  `Overlay.lean` no longer require `MaximumBoundsValues`. The three new lower
  lemmas and five strengthened public lemmas use only standard Lean axioms.
  The lower proofs are `f0daba3`; public integration is `aa023cf`. The content
  contracts' former semantic maximum premise is generalized by the skipped-
  suffix foundations above.
- `ProgressiveList/ApplyUpdates/Overlay.lean` proves exact representation
  criteria using the actual rebuilt values and installed default map. No
  separate clone-identity or empty-default law is needed by these criteria;
  the all-branch result requires backing/layout/range laws only on
  nonempty application. `Contents.lean` derives actual rebuilt backing reads
  without default-map laws, and `Materialized.lean` identifies the stored
  sequence under selected clone preservation. `Total.lean` uses these facts
  to derive complete representation/backing/observer contracts with exact
  default overlay and extent. `Conditions.lean` proves successful preservation
  equivalent to the actual empty-map no-op or occupied final capacity and an
  actual default outcome with those map laws, under the stated selected clone
  and metadata assumptions. Pending emptiness supplies only its observer.
  Existing empty-map content and total contracts use the new foundations.
  `len_after_apply_updates_iff` gives exact equality of complete length results
  without representation, packing, clone, range, or successful-map premises;
  the no-op also preserves failure/divergence. All nine new lemmas use only
  standard Lean axioms. Length integration is `8e80e9c`, success criteria
  `5823c1f`, total contracts `40ac435`, materialization `decf6f7`, and overlay
  foundation `c338515`. These results audit default-map laws; remaining clone,
  range, geometry, and source-fidelity reviews are separate obligations.
- `ProgressiveList/Arbitrary/Overlay.lean` characterizes representation of
  the actual generated sequence by the default map's overlay and logical
  extent. `Conditions.lean` proves exact execution and sequence-preservation
  criteria from a finite control/element trace, occupied-layer `LengthFits`,
  and an actual default outcome; no trace or default success is a premise.
  The trace retains the actual final input, without restricting element
  consumption, retention, or replacement of input. `Traits.lean` extends
  both criteria and representation equivalence to the actual owning default,
  recovering the final input discarded by its ordinary generator call.
  `Generated.lean`, `Total.lean`, and `Traits.lean` derive the complete
  representation/backing/spine contracts using exact map conditions; pending
  emptiness supplies only its observer. The existing empty-map contracts are
  adapters. All nine new lemmas use only standard Lean axioms. Owning trait
  integration is `16befa3`, success criteria and total generation `f93004f`,
  and representation foundation `b8f058f`. These results audit default-map
  laws under packing layout and the external generator model; remaining
  geometry/premise and source-fidelity reviews are separate obligations.
- `ProgressiveList/Decode/Overlay.lean` characterizes representation of the
  actual decoded sequence by the installed default map's overlay and logical
  extent. `OverlayTotal.lean` combines these laws with an actual input-bound
  payload trace and occupied-layer `LengthFits` for an exact public success
  and representation criterion. Successful execution recovers the consumed
  payloads, and `PublicTrace.lean` proves agreement with any supplied complete
  trace without packing, codec, or map laws. The trace total contract derives
  execution, represented contents, valid backing, exact stored values/count,
  and installed map. Fixed- and variable-format total contracts also use the
  exact map conditions; the existing empty-map contracts are adapters. Pending
  emptiness is separate and used only for its observer. Empty bytes still need
  no packing or element metadata. The general `represents_nil_iff` proves
  that representing an empty sequence requires exactly zero backing length,
  absent maximum, and absent reads, with no tree or packing premise. All nine
  new lemmas use only standard Lean axioms. Public format integration is
  `decd3f9`, trace criteria `5c49998`, and representation foundation `5b8202a`.
  Remaining geometry, codec-premise, and external-model fidelity reviews are
  separate obligations. The Arbitrary checkpoint above extends the default-map
  criteria to both generator entry points.
- `ProgressiveList/Construction/Overlay.lean` specializes the same-length
  representation equivalence to all four sequence constructors. The actual
  default map must overlay the consumed values to themselves and preserve
  their logical extent; redundant matching entries and maxima below the
  input length are permitted. `OverlayConditions.lean` combines these laws
  with actual finite consumption and occupied-layer `LengthFits` for exact
  success-and-representation criteria. Iterator traces are recovered from
  execution and proved equal to the actual stored sequence; vector callers
  need no iterator premise. These criteria need no pending-emptiness law.
  The four generalized contracts in `Total.lean` derive execution, represented
  contents, valid backing, and valid spine internally, using a separate
  emptiness law only for the pending observer. Existing representation and
  total specifications use the empty-map special case as an adapter.
  All twelve new lemmas use only standard Lean axioms. The success criteria
  are `a756c07`, total contracts `a32454f`, and representation foundation
  `75701ea`. Packing layout, geometry, and external-model fidelity retain
  their separate audit obligations.
- `ProgressiveList/Overlay.lean` characterizes representation when the
  target length equals the recorded backing length: the actual pending map
  must overlay the backing to the target and its maximum must preserve logical
  extent. Empty map reads and an absent maximum are sufficient adapters, not
  necessary conditions; redundant pending values and maxima below the backing
  length are allowed. `PopFront/Overlay.lean` specializes this to the actual
  cloned backing after successful nonzero removal. `OverlayTotal.lean` proves
  exact success-and-representation criteria from the removal bound, occupied
  retained capacity, actual ordered clone outcomes, and actual default-map
  overlay/extent. Clone identity is not separately assumed: the criterion
  concerns the effective merged result. The all-count criterion omits every
  clone/default obligation on zero removal and requires layout/backing laws
  only for a nonzero in-bounds rebuild. Its complete nonzero total contract
  derives execution, represented suffix, valid backing, exact cloned contents,
  recorded length, and installed default map. Pending emptiness is a separate
  law used only for the observer. Existing dense-backing representation,
  front-removal content, and total contracts use these results as adapters.
  These proofs use only standard Lean axioms. Public total integration is
  `45f8783`, with representation adapters `7801d06` and the general overlay
  foundation `9dd67d2`. Geometry, source representation, and external-model
  fidelity retain their separate audit obligations.
- `ProgressiveList/Rebase/Lookup.lean` proves preservation of complete
  backing/public lookup results for in-place rebasing, including map failure,
  divergence, and indices beyond the backing length, without a representation
  or successful-map-read premise. For nonmutating rebasing, fallback-aware
  agreement with the actual returned map is necessary and sufficient for
  each lookup and for all reads. `Representation.lean` proves in-place
  representation equivalence without assuming input representation, and
  `rebase_represents_iff` makes the actual map's read/extent conditions exact
  for preserving an already represented sequence. `SelectedTotal.lean` proves
  successful sequence-preserving execution equivalent to `RebaseReady` and,
  for nonmutating rebase, an actual map-clone outcome with those read/extent
  laws. Its total contracts derive success, represented contents, backing
  validity, and metadata internally. Existing content and total contracts,
  including downstream total cache contracts, now use these results. Packing
  layout and backing geometry still justify indexed traversal; selected
  content soundness remains explicit. The clone conditions are exact under
  these premises, without asserting minimality of every other premise or
  external-model fidelity. Public total integration is `594f218`, with
  representation `eef66e2` and lookup foundations `297cfd4`.
- `ProgressiveList/Rebase/SelectedCaches.lean` proves
  `rebase_on_cache_iff_of_inputs` and `rebase_cache_iff_of_inputs`: under the
  selected `RebaseContentInputs` soundness law and actual success, result
  cache validity is equivalent to `RebaseCacheInputs`. No packing layout,
  geometry, density, capacity, accurate-length, query-success, pending-map,
  or representation premise is needed. The binary scope selects original,
  base, or rebuilt-node caches at the supplied optional lengths and full
  depth; cache-subject depth is independent and may be zero. Progressive
  scopes retain original suffix caches on immediate stops and use actual
  packing queries and clamped lengths for entered layers. Base progressive
  caches are never imported. `SelectedKindReflection.lean` derives the exact
  action category from execution using only standard Lean axioms; both
  general and dense-input classifier proofs omit the pointer contract.
  Existing binary/progressive/public cache contracts now use the general
  equivalence through dense-input adapters. The cache-input criterion is
  necessary and sufficient under the selected content law; minimality of
  that semantic law and the remaining assumption/model-fidelity audit are
  not claimed complete. Public integration is `e88ce19`, with progressive
  foundations `2307f24`, binary results `c20e293`, cache scopes `c31c8bb`,
  classifier foundations `9db36ad`, and the axiom reduction `f9da88a`.
- `ProgressiveList/Rebase/SelectedContents.lean` proves exact backing-content
  preservation for both public rebase methods from actual success and
  `RebaseContentInputs`. Binary content laws use the supplied optional lengths
  and full depth; progressive laws use the actual packing-query results and
  both machine clamps in layer lengths. No layout, density, shape, capacity,
  accurate-length, comparison-termination, or query-success premise is needed
  for materialized contents. Missing/shared suffixes require no semantic law;
  selected pointer, element, and hash shortcuts determine the remaining laws.
  `Rebase/Contents.lean` adds `rebase_on_spec_of_content_inputs` and
  `rebase_spec_of_content_inputs` for the represented merged sequence. These
  retain geometry/layout for indexed traversal and, for nonmutating rebase,
  fallback-aware map-clone read agreement and matching logical extent.
  Existing binary, progressive, and public content contracts now use the
  general results through dense-input adapters. Semantic soundness remains
  explicit; no necessity or complete assumption-minimality claim is made.
  Public integration is `c8724e7`, with public backing results `78d9600`,
  progressive contents `b166ec0`, progressive input laws `aa0bb68`, and binary
  foundations `1fa4dbc`, `47c372e`, and `5832bf5`.
- `ProgressiveList/Rebase/Ready.lean` proves `rebase_on_success_iff_ready`
  and `rebase_success_iff_ready`, with no separate packing-layout or global
  query-success premise. `RebaseReady` permits an immediate missing/shared
  input stop without packing queries; otherwise it requires the actual query
  results and the selected arithmetic/geometry/element-call conditions.
  Nonmutating rebase additionally requires its actual pending-map clone to
  return, including on tree shortcuts. Progressive `Ready.lean` recovers the
  queries from actual entered-node execution and proves both directions.
  `PackingQueries.lean` records factor and defaulted-depth results without
  positivity or power-of-two/coherence laws, and retains the actual logarithm
  outcome for packed factors. `Steps.lean` now has a decomposition requiring
  only the depth query, with the old layout theorem retained as an adapter.
  Existing total success proofs use the complete public criterion. Packing
  and geometry for traversal/cache correctness and model fidelity remain
  separate obligations; the later selected-content results above remove these
  premises for materialized contents. The public/integration checkpoint is `3231f6f`, with
  foundations `d1ba797`, `4952ade`, and `cb7e79e`.
- `ProgressiveList/Rebase/SelectedConditions.lean` proves the general public
  criteria `rebase_on_success_iff_requirements` and
  `rebase_success_iff_requirements`. Given the actual packing query results,
  selected input requirements are necessary and sufficient, plus the actual
  pending-map clone's termination for nonmutating rebase. The original fixed
  layout premise was weakened in `4952ade`. No whole-tree shape or
  representable-layer invariant is assumed. `Tree/Rebase/GeometryInputs.lean`
  and `GeometrySuccess.lean` characterize only reached shape/depth/shift checks,
  omitting every check bypassed by pointer, zero-input, and hash shortcuts.
  Progressive `Requirements.lean` retains the actual clamped layer lengths;
  `SelectedSuccess.lean` derives all depth/capacity calculations and recursive
  calls and reflects them from success. Existing progressive and public
  success lemmas now use the general proof through invariant adapters, so the
  existing total contents/cache contracts build on it. These results remove
  the global geometry premises from success criteria; geometry for content
  and cache correctness, packing assumptions, and model fidelity have separate
  audit obligations. The public/integration checkpoint is `2d63438`, with
  foundations `15af31a`, `9e1c78c`, `9afa364`, and `dfe9e73`.
- `ProgressiveList/Rebase/Conditions.lean` proves `rebase_on_success_iff`
  and `rebase_success_iff`: under packing layout, compatible shapes, and
  representable original layers, public success is equivalent to termination
  of the selected element comparisons, plus termination of the actual
  pending-map clone for nonmutating rebase. No comparison success, density,
  accurate recorded lengths, semantic equality/hash law, or map-preservation
  law is assumed. `Rebase/SuccessReflection.lean` at both tree levels recovers
  the comparison scopes from actual successful calls, including child calls
  followed by final pointer reuse. Binary reflection needs no geometry;
  progressive reflection needs only layout and original capacity. The Arc and
  vector equivalences in `ComparisonReflection.lean` retain pointer and
  short-circuit behavior, with no laws on omitted comparisons. These are exact
  termination criteria under the stated geometry; the general selected-input
  criteria above supersede that restriction. The public checkpoint is
  `d5836d4`, with foundations `3f2f4fa`, `c3ff39d`, and `212ac40`.
- `ProgressiveList/Rebase/CacheEquivalence.lean` proves `rebase_on_cache_iff`
  and `rebase_cache_iff`: validity of the successful result is equivalent to
  the retained-original and imported-base cache laws together. The equivalence
  retains the semantic content laws and input geometry, and assumes no cache
  validity, represented sequence, or pending-map clone/read/maximum law.
  Binary and progressive `Rebase/CacheReflection.lean` recover both input laws
  from actual output validity, including final pointer reuse of progressive
  nodes. `CacheAction.lean` derives the relevant inputs from each source
  combination branch. The proof checkpoint is `ad4e3f4`, with foundations
  `0dc26d2` and `01b05f5`.
- `Tree/Rebase/OriginalCaches.lean` and its progressive counterpart define
  `RebaseOrigCachesOn` for original caches retained by the actual action.
  Whole-base replacement needs no retention law for discarded original
  caches. `Rebase/HashInputs.lean` at both levels separately scopes original
  validity to reached nonzero hash shortcuts. Full original validity supplies
  both laws through adapters. Eight successful-execution/total public cache
  contracts use these weaker original premises (`01f0d4f`, foundations
  `a653121`, `8173c77`); the all-returned-states wrapper retains full original
  validity because errors restore the original tree. Cleared-input contracts
  derive both laws internally. The progressive step certificate now retains
  completed child calls when final pointer checks reuse the original node,
  allowing the selected-cache induction to cover that optimization.
- `Tree/Rebase/Kind.lean` classifies inputs using the actual pointer, element,
  hash, and action-combination decisions. `KindReflection.lean` proves that
  every successful extracted rebase returns that category at accurate dense
  metadata, without element/cache soundness or comparison-termination laws.
  The classifier retains the source's ordered mixed-equality cases; no claim
  that a `NotEqual` action establishes semantic inequality is made.
  `Tree/Rebase/CacheInputs.lean` requires no base validity for no-ops, full
  base validity for whole-base replacement, and selected child-cache validity
  for rebuilt nodes. Its adapters and child-scope lemmas feed binary cache
  preservation and the finite-collision bridge.
  `ProgressiveTree/Rebase/CacheInputs.lean` uses this binary scope within
  reached layers, retaining absent/shared-suffix pruning. All eleven public
  rebase cache/validity contracts use the weaker law (`99fad96`, foundation
  `b7e16e2`). The original-cache refinements and joint cache-validity
  equivalences are recorded above. The equivalences retain the semantic
  content and input-geometry assumptions; those assumptions and remaining
  model fidelity have their own audit obligations.
- `Tree/Rebase/PackedSoundness.lean` restricts packed element soundness to
  vectors whose paired `ne` calls all return false. It proves this guarded
  law necessary and sufficient for sound positive vector equality, and derives
  it from the previous reached-pair law. A true, failed, or diverging paired
  call removes every soundness obligation for that vector, including earlier
  false answers. `Tree/Rebase/Soundness.lean` uses the weaker law in all
  dependent binary, progressive, and public list rebase contents/cache
  contracts. Length, pointer, and hash shortcuts retain their existing scope.
  The proof and validation checkpoint is `fbf2a27`, with foundation `e9ada7a`.
- The [Arbitrary source comparisons](reproducers/arbitrary_models/README.md)
  validate collection control against actual `bool::arbitrary`, including
  the actual byte generator and one-byte fill/zeroing loop. It proves the
  Boolean result and exact remaining input for every slice, consuming even
  stopping bytes and returning false at exhaustion, without extra premises.
  The proof uses only standard Lean axioms and retains array/slice/iterator,
  scalar, copy, and Result foundations. Both size-hint defaults also match their
  source bodies for arbitrary dictionaries and depths: the fixed default skips
  callbacks, while the fallible default preserves the actual hint callback's
  success, failure, or divergence. Eight native tests check vector error/panic
  state, input replacement, and default dispatch, including hint panics.
  Full vector generation and the owning default remain source boundaries
  (UPSTREAM_BUGS 27). At `e396dad`, all seven source suites pass: 32 direct
  comparisons and two compositions, totaling 34 proofs (16 axiom-free,
  eighteen standard-only).
- The [SSZ source comparisons](reproducers/ssz_offset_models/README.md)
  validate the actual four-byte constant and private decoder for every input
  length, including the complete copy loop and exact error payloads. A separate
  composition proof relates prefix slicing followed by that decoder to the
  public-reader model. All three use only standard Lean axioms, without extra
  length, copy-success, termination, or word-bound premises. The runner verifies
  that retaining the private root and renaming its source error type changes
  only the declared metadata. Direct public-reader extraction and the encoder's
  missing `Usize.to_le_bytes` foundation remain unresolved (UPSTREAM_BUGS 26).
  Encoder construction also matches its actual source, including the buffer
  release continuation, relative to the existing local `Vec::reserve` model.
  This comparison uses only `propext`; reservation fidelity remains a separate
  boundary. The audit imports the concrete model and never compiles the
  generated axiom template. Append/finalize fail on borrowed-buffer access.
  Eight SSZ native tests and all seven source suites pass at `4cbc263`: 33 direct
  comparisons and two compositions, totaling 35 proofs (16 axiom-free, nineteen
  standard-only). Existing byte/array/slice/scalar foundations are retained.
- The [vector source comparisons](reproducers/vec_models/README.md) validate
  `is_empty`, `eq`, and `ne` for arbitrary vector values and comparison
  dictionaries. They preserve empty/length shortcuts, element `ne` dispatch,
  and failure/divergence without consistency or termination assumptions.
  The audit exposes the actual comparison bodies by changing only temporary
  declaration names and verifying the entire remaining LLBC is unchanged.
  The proofs use only standard Lean axioms and retain vector/index/slice
  foundations. Six native tests additionally check moves, capacity, mixed
  iteration, zero-sized elements, and drops. Direct `pop`/`next_back` source
  extraction remains unresolved (UPSTREAM_BUGS 25); native evidence does not
  replace that obligation. All five then-existing source suites pass at
  `1a575ec`.
- The [tuple source comparisons](reproducers/tuple_models/README.md) validate
  `eq`, `ne`, `partial_cmp`, and `cmp` against fresh extraction of the pinned
  standard-library bodies for arbitrary callback dictionaries. Short-circuiting,
  failure, and divergence match without consistency or termination premises.
  Equality and inequality are axiom-free; the ordering comparisons use only
  the existing models' `propext`. Four native tests check 59 answer combinations
  and exact dispatch/order. Omitting four unused, unsupported trait defaults
  leaves all four expanded source declarations unchanged; the runner checks
  this on each run and rejects incomplete generated output. All four source
  audit suites pass. The broader `PartialOrd` interface is not covered.
- The [fixed-byte source comparisons](reproducers/fixed_bytes_models/README.md)
  validate clone, equality, ZERO, default, and `is_zero` against the actual
  pinned `alloy-primitives` bodies used by cache initialization and rebasing.
  All five comparisons hold for every length and byte array without additional
  premises, retaining the existing Aeneas array/byte foundation. Clone is
  axiom-free; the others use only standard Lean axioms. Their source audit and
  four native tests pass, as do the core and Option suites after extending the
  shared runner for locked Cargo dependencies and constant initializers.
- The [power source comparison](reproducers/pow_models/README.md) validates
  the entire extracted `usize::pow` body for every base/exponent and either
  compiler-selector outcome (`eb2f91b`). Both loops, zero exponents, and exact
  overflow failure are covered, without an arithmetic or termination premise.
  The proof uses only standard Lean axioms. The selector remains abstract,
  represented by one arbitrary Bool parameter because the outer body calls it
  at most once. All extracted function bodies remain unchanged; the runner
  validates this and reports a separate parameterized source comparison.
  Existing Aeneas scalar primitives remain a foundation boundary.
- The [core source comparisons](reproducers/core_models/README.md) validate
  `Result::map_err` and `hint::must_use`, reached by SSZ decoding, blanket
  `Borrow::borrow`, and `mem::take`, used for pending-map rebuilding,
  `usize::div_ceil`, used in
  builder finalization, and `u128::saturating_mul`/`u128::checked_pow`, used in capacity arithmetic,
  against their actual extracted standard-library bodies.
  Default results are unconstrained; zero-divisor failure and rounding safety
  are covered for every machine-word input without an arithmetic premise.
  Saturation and checked power cover every input and overflow, retaining
  Aeneas's existing checked-multiplication primitive. Checked-power termination
  and its accumulator invariant are derived from the actual loop and initial
  state. `map_err` preserves arbitrary callback success, failure, and divergence;
  the borrow and hint comparisons establish their runtime value behavior in
  the existing reference abstraction. These three adapter proofs and `take`
  are axiom-free; the three numeric comparisons use only standard Lean axioms.
  The source audit and eleven native
  tests pass. Remaining intrinsic boundaries are recorded in UPSTREAM_BUGS
  issue 24.
- The [Option source comparison](reproducers/option_models/README.md) checks
  eleven local Option models against independent extraction of their actual
  pinned standard-library bodies. A twelfth theorem verifies `cloned` through
  the source's map-and-clone composition; direct extraction of its function
  item remains unsupported (UPSTREAM_BUGS issue 23). All checks are axiom-free
  and permit arbitrary callback results. Their separate audit verifies source
  provenance, complete generated bodies, and native clone protocol behavior.
  These standalone checks retain Aeneas's reference/drop abstraction and are
  not included in the main `Tree` theorem count.
- `Tree/PackingDepth.lean` derives the actual packing-depth query from the
  optional factor query and, for packed elements, the required power-of-two
  law. `Tree/Nat/NextPowerOfTwo.lean` proves that rounding preserves an exact
  power of two; the existing trailing-zero valuation proof then computes its
  logarithm. The represented factor supplies the word bound, so the proof
  skips the `size_of` fallback without using its axiom or a separate bound.
  `PackingLayout` now contains only the factor query and power law. Its
  `opt_packing_depth_eq` accessor derives the depth result. Both constructors
  drop their former `depth_eq` argument, and all builder/repeat callers are
  updated. Every public specification using this layout inherits the simpler
  contract; the routing power-of-two requirement remains.
- `Tree/Tuple/Comparison.lean` proves the actual external tuple inequality
  protocol: first-true short-circuiting, exact second-call delegation after a
  false first result, first-call failure/divergence, and both Boolean success
  characterizations. The model now calls element `ne`, as the pinned Rust
  source does, without an extra coherence law relating `eq` to `ne`. Native
  protocol regressions confirm dispatch and order. The dictionary appears in
  the conservative `apply_updates` dependency closure through optional hash
  lookup; the progressive path supplies `None`, which the existing binary
  update proofs reduce without reaching that lookup.
- `Tree/ProgressiveTree/Builder/Trace.lean` derives the finite sequence of
  actual iterator calls from every successful extension, through its first
  `none`, and proves exact appended elements and length. No finiteness,
  packing, builder-invariant, or fused-iterator premise is supplied.
  `ProgressiveTree/Construction/Trace.lean` lifts this to actual construction:
  the input yields precisely the materialized tree elements and returned
  count. `ProgressiveList/Construction/Trace.lean` proves the corresponding
  public input trace, exact length, and actual default map with no iterator,
  packing, or map law. Its indexed-sequence specification adds only packing
  and the actual default map's empty laws and establishes backing/spine
  validity and no pending updates.
  `Construction/Conditions.lean` characterizes success of `try_from_iter` and
  its SSZ trait entry point by finite actual conversion/next calls, occupied
  layer capacity, and successful default-map construction. The vector `new`
  and `TryFrom<Vec<T>>` criteria derive their iterator behavior internally and
  require exactly capacity and default-map success. No successful-default or
  finite-input assumption is imposed before these equivalences. The existing
  finite-input total contracts and capacity-only specializations remain
  available. Packing remains a premise: the generic constructor initializes
  its builder before converting or reading even an empty iterator.
- The canonical fixed and variable decoder contracts in `Decode/Fixed.lean`,
  `FixedTotal.lean`, `Variable.lean`, and `VariableTotal.lean` now require
  element metadata and packing layout only for nonempty contents. Fixed
  positivity and occupied-layer capacity are conditional as well. Empty
  contents retain the actual default-map construction and its relevant empty
  behavior, without assumptions about skipped decoder calls or construction.
  `FixedRoundtrip.lean` and `VariableRoundtrip.lean` also require decoder
  metadata only for nonempty contents; fixed decoder positivity and capacity
  are conditional. Their encoder and traversal premises still describe calls
  made by the actual encoder. The theorem names are retained, with weaker
  hypothesis types; callers were updated and verified.
  `Decode/PublicTrace.lean` factors materialized-sequence representation,
  valid backing, and no pending updates into `from_ssz_bytes_represents`.
  The trace specification and both canonical sequence specifications reuse
  this format-independent result rather than duplicate state reasoning.
- `Tree/ProgressiveList/Decode/Trace.lean` derives a finite annotated payload
  trace from every successful streaming result, including partial lists
  finalized at a decoding error. It then recovers the exact stored values,
  recorded count, and actual default map, without a supplied parser trace,
  builder invariant, packing law, or element-codec law.
  `Decode/State.lean` now retains the public decoder's actual empty-input
  branch or nonempty metadata and cursor initialization; its previous state
  projection reuses that stronger theorem.
  `Tree/Ssz/DecodedBytes.lean` describes complete input parsing with individual
  accepted payloads and no list-construction call. `Decode/PublicTrace.lean`
  derives this input-bound trace from any successful public decoder call and
  proves indexed representation, backing validity, and no pending updates
  under the actual default map's empty laws and packing layout only for
  nonempty input. No canonical encoding or supplied element-result sequence
  is required. `Decode/Conditions.lean` proves success is equivalent to such
  a complete trace, occupied-layer capacity, and a successful default-map call.
  Both necessity and sufficiency are proved; the criterion needs no map-content
  or codec law, and empty input needs no packing or element metadata.
- `Tree/Ssz/PayloadSuccess.lean` derives complete fixed and variable cursor
  traces from per-occurrence payloads, including distinct accepted encodings
  of equal values. It also proves an accepted short final fixed chunk follows
  the full-width prefix. Erasing the proof-level payload annotations recovers
  the actual element-decoder traces consumed by the list builder proofs.
  `ProgressiveList/Decode/PayloadFixed.lean` and `PayloadVariable.lean` lift
  these traces to total public decoding with exact indexed contents, valid
  backing, and no pending updates. Empty input requires no element metadata,
  layout, or capacity law. Variable capacity follows from the offset table;
  only stored offsets need 32-bit bounds, with no final-payload-end bound.
  The earlier canonical-encoding contracts and roundtrips remain available.
- `Tree/ProgressiveList/PopFront/BuilderClones.lean` recovers actual ordered
  clone results, appended contents, and the exact count from successful
  streaming execution. It needs neither clone laws nor builder validity.
  `Builder.lean` and `BuilderLength.lean` derive their original contents/count
  contracts from this shared proof. `BuilderTotal.lean` requires only successful
  retained clones and occupied final capacities to prove execution success.
  `Clones.lean` lifts exact clone behavior through actual public iteration,
  rebuilding, finalization, and default construction. `Contents.lean` and
  `Length.lean` reuse it, removing duplicate reconstruction arguments.
  `ClonesTotal.lean` represents the actual retained clone results at every index,
  preserving their count and establishing valid backing and no pending updates
  under the relevant default-map laws. The original `Total.lean` identity-clone
  contract is a specialization.
  `Conditions.lean` proves all four nonzero success conditions necessary and
  sufficient: the removal bound, occupied retained capacity, successful retained
  clones, and successful default construction. Zero needs no laws. Representation
  is scoped to nonzero calls, and layout/backing invariants to in-bounds rebuilds;
  the criterion needs no clone identity or default-map semantics.
  `Capacity.lean` derives its earlier capacity-only criterion from this result.
- `Tree/ProgressiveList/Iter/Bounds.lean` characterizes every returned
  read-only constructor error by the actual logical length and oversized
  start. Its out-of-bounds theorem now derives the length computation directly
  from optional maximum metadata and the numeric comparison, replacing the
  former full sequence-representation premise. No indexed reads, backing,
  packing, unchecked-constructor success, or separate successor bound is needed.
  `IterCow/Bounds.lean` proves exact agreement with those errors and the constant
  original-list continuation. Its metadata theorem reuses the read-only proof,
  and `IterCow/State.lean` reuses the equivalence for restoration. Accepted
  constructor enumeration and pending-overlay invariants remain unchanged;
  these bounds results do not prove borrowed CoW stepping.
- `Tree/ProgressiveList/IsEmpty.lean` derives the public observer from the
  actual optional maximum and the necessary-and-sufficient successor bound,
  without assuming successful length evaluation or sequence representation.
  Its exact true-result equivalence has no premises: recorded backing length
  is zero and the actual maximum query returns none. The map's separate
  emptiness method is not used. This is metadata behavior, not a claim of
  indexed-sequence agreement for malformed maps.
- `Tree/ProgressiveList/Push/Total.lean` proves the complete public append
  operation: below the machine limit it succeeds and represents the old
  sequence followed by the appended value; at the limit it returns `ListFull`
  with the entire input unchanged. Both branches preserve the exact backing
  tree and recorded backing length. Only the actual nonfull insertion needs
  termination, maximum, and lookup laws; no clone, structural capacity,
  backing-validity, previous-value, or successful milhouse-subcall premise is
  assumed. `Push/State.lean` characterizes every returned Rust error without
  representation or map laws. `Push/Capacity.lean` derives success and
  `ListFull` criteria directly from optional maximum metadata, without indexed
  reads or representation. Only the success direction needs the reached
  insertion to terminate; overflowing maximum successors remain distinct from
  returned Rust errors. `len_after_push_iff_max_index` proves exact length
  growth is equivalent to the returned map maximum being the appended index,
  without lookup or structural laws or a separate capacity bound.
  `Push/Maximum.lean` proves the corresponding sequence-append equivalence
  under the reached insertion's lookup law. The existing length and total
  append proofs reuse these criteria; their exact maximum premise is necessary.
  `Push/Lookup.lean` weakens the lookup law to the exact new pending value at
  the appended key and agreement after the original backing fallback at other
  keys. It proves the public-read criterion, retaining failure/divergence and
  requiring the backing bound only for an appended-key query. The new boundary
  lemma identifies public reads with raw map answers outside backing, and an
  adapter derives the new contract from exact insertion/lookup equality.
  `push_represents_append_iff` proves lookup and maximum conditions jointly
  necessary and sufficient for the full append sequence, without assuming a
  read law or extra bounds. The total append proof uses that joint criterion.
- `Tree/ProgressiveList/ApplyUpdates.lean` now retains the actual nonempty
  answer in the successful-state characterization. Empty-map, pending-observer,
  idempotence, and logical-length results require default-map laws only when
  that branch constructs the default. `ApplyUpdates/Contents.lean` and
  `Backing.lean` likewise condition packing, clone, range, maximum, and default
  laws on the actual nonempty branch, retaining their complete sequence and
  backing conclusions. The existing total and capacity contracts use the
  weakened successful-execution results. Input backing validity remains:
  density permits empty materialized layers, so occupied-length capacity alone
  cannot justify the capacities of every retained layer.
- `Tree/UpdateMap/Length.lean` and `Tree/ProgressiveList/Length.lean`: exact
  total helper/public length results from the actual optional maximum. Success
  is equivalent to a representable successor for a present maximum, with no
  map-read, representation, density, or packing law. Absent maxima return the
  backing length, and present maxima return its maximum with the successor.
  `updated_length_eq_ok_iff` characterizes each successful machine-length
  result by the raw maximum and its mathematical extent, deriving the
  successor bound from that target. `updated_length_succ_iff_max_index` proves
  that extending beyond the backing length requires the exact final index and
  a representable successor.
- `Tree/ProgressiveList/Encode/FixedLength.lean`: the fixed-width operation
  preserves the exact length and multiplication failure/divergence behavior.
  The numeric specification needs only logical length, replacing the former
  full sequence representation. The total specification derives length from
  returned maximum metadata and bounds; no successful milhouse subcall is
  assumed. Success is equivalent to successor representability and the final
  byte bound, also for malformed metadata and zero-width elements.
- `Tree/ProgressiveList/PopFront/Total.lean`: packing layout is required only
  for nonzero removal, matching the existing conditional rebuilding laws.
  The complete retained-sequence and backing-validity conclusions are unchanged.
- `Tree/Rebase/ComparisonInputs.lean` retains optional supplied lengths and
  defines the exact left/minimum and right/remainder split at each full depth.
  The actual Rust callback supplies those inputs without density or recorded
  length/content agreement. `Tree/Rebase/Comparisons.lean` now guards every
  binary recursion by pointer inequality, positive depth, and the actual
  optional-length hash guard. `ProgressiveTree/Rebase/Comparisons.lean` supplies
  each binary scope with its clamped layer lengths and full depth; existing
  geometry lemmas derive those values from actual metadata calculations.
  All 13 binary/progressive/public success and total-operation interfaces use
  this scope, with no added capacity, density, clone, map, or subcall-success
  premise. A selected hash shortcut discharges comparison termination directly.
- `Tree/Rebase/ElementComparisons.lean` describes only external element `ne`
  calls reached by the packed comparison loop. A false answer continues and
  a true answer stops, leaving all subsequent calls unconstrained. The law
  implies successful execution of the actual external `anyM` loop, and every
  successful loop execution supplies the law. `vec_eq_success` and the complete
  rebase success chain use this weaker condition. Ordinary termination on all
  paired inputs remains a sufficient way to establish it; no comparison
  completeness, reflexivity, element cloning, or equality law is added.
- `Tree/Rebase/Pointer.lean` and `ProgressiveTree/Rebase/Pointer.lean`
  prove the actual early-return behavior at arbitrary depths and lengths and
  discharge comparison, equality, and cache-shortcut laws without examining
  descendants. They also prove the finite collision input collection is empty.
  `ProgressiveList/Rebase/Pointer.lean` lifts the actual branch to an exact
  unchanged in-place result and an exact nonmutating pending-map-clone
  equation, including clone failure and divergence. Neither public equation
  assumes representation, shape, packing, cache validity, element behavior,
  or a generic map law. The existing pointer model supplies shared-value
  equality for the complete unchanged-list result.
- `Tree/Rebase/HashShortcut.lean` states the stored-byte/length guard without
  a hash-computation or collision assumption. `HashShortcutSteps.lean` proves
  immediate successful replacement by the base whenever the actual pointer,
  positive-depth, nonzero-hash, hash-equality, and optional-length guards select
  that branch. It needs no child-shape, comparison, recursive-success, or
  collision law. The contents/cache inductions separately apply collision
  soundness only on that branch and recurse only when it is not selected.
- `Tree/Rebase/Soundness.lean` proves Arc equality soundness for just the
  compared pair. `ContentsAction.lean` uses the shared element-soundness proof
  to derive vector contents agreement from false-`ne` soundness on reached
  input pairs. Pointer shortcuts, unequal-length vectors, and packed pairs
  after the first true `ne` need no element law. Binary
  and progressive `RebaseEqualitySound` predicates restrict the laws to
  corresponding input leaves and layers, with no conditions on unrelated
  values or pending updates. The existing global soundness laws imply these
  weaker predicates. All 21 binary, progressive, and public list rebase
  contents/cache specifications now use them, including both total variants,
  reference-valid caches, error-state preservation, and cleared original
  caches. Binary and progressive pointer checks now guard all recursive
  scopes, omitting descendants of shared subtrees. The equality scope also
  skips descendants after a nonzero equal-hash/equal-length shortcut; density
  connects its materialized lengths to the supplied Rust metadata. Comparison
  termination now uses the supplied optional lengths and full depth, follows
  exact child splits, and likewise skips descendants below cache shortcuts.
  Packed comparison termination and soundness both stop at the first true
  element `ne`; `NeOn.of_pairs` derives the weaker soundness scope from laws
  on every supplied pair. Duplicate vector soundness proofs have been removed.
- `ProgressiveList/Caches.lean` preserves arbitrary predicates on backing
  caches through every returned push state, mutable and CoW write-back,
  cloning, and both CoW iterator constructor continuations. Exact backing-tree
  preservation needs no zero-sentinel, map, clone, representation, or shape law.
- `Tree/HashCache/Collisions.lean` defines a finite collection of corresponding
  binary hash-input pairs selected by pointer/cache guards. Shared subtrees
  contribute nothing; a nonzero equal-hash/equal-length shortcut contributes
  only its root pair. Otherwise both corresponding children are followed.
  Zero-cache, different-hash, and unequal-length roots contribute no pair.
  Its reference collision law applies only to equal-length pairs with an equal
  nonzero reference hash; no global injectivity premise is used. Valid stored
  caches imply the similarly pruned operational `CachedHashesAgree` law under
  this finite condition. `ProgressiveTree/Rebase/Validity.lean` lifts
  the bridge across corresponding layers and requires only binary cache
  validity, excluding both trees' progressive caches. Cleared original trees
  have no collision inputs and satisfy operational cache agreement against
  any base without a reference or base-validity premise.
- `ProgressiveList/Rebase/Validity.lean` combines that bridge with successful
  and total public rebasing and preserves reference cache validity on every
  returned in-place state. The base needs only binary cache validity because
  its progressive caches are never imported. `Rebase/Cleared.lean` discharges
  collision soundness and original reference-cache validity internally from
  cleared caches for both total public rebase operations. These results close
  the reference-validity-to-shortcut bridge; they do not supply or prove the
  still-unextracted semantic hash computation or shared cache writes.
- `Tree/HashCache/Cleared.lean` gives a depth-independent invariant for
  freshly initialized caches and bridges it to every predicate accepting zero.
  `Tree/Builder/Caches/Push.lean` and `Finish.lean` track it through the actual
  carries, packed-leaf extension, finishing merges, zero padding, and final
  stack extraction. `ProgressiveTree/Builder/Caches.lean` and
  `Caches/Iterator.lean` lift clearing through fresh builders, subtree rollover,
  spine assembly, and iterator consumption. No shape, counter, packing,
  element-hashing, map, clone, or termination laws are needed for these
  successful-execution cache invariants.
- `ProgressiveTree/Construction/Caches.lean` and
  `ProgressiveList/Construction/Caches.lean` prove cache initialization through
  every currently extracted inherent constructor and conversion trait,
  including empty/default. `Construction/CacheTotal.lean` composes reference
  cache validity with all four existing total constructor specifications
  without adding premises. `Decode/Caches.lean` covers the actual streaming
  decoder and public SSZ entry point, including partial lists finalized after
  element errors. `Arbitrary/Caches.lean` covers both generation entry points.
  `PopFront/Caches.lean` proves actual streaming reconstruction initializes
  cleared caches on nonzero success and preserves reference cache validity on
  every returned state. These are initialization/preservation results; actual
  semantic hash computation and shared cache writes remain outstanding.
- `Tree/BulkUpdate/Caches.lean` and
  `Tree/ProgressiveTree/BulkUpdate/Caches.lean` prove cache-invariant
  preservation by induction on the actual extracted fixed points. Rebuilt
  caches are zero; untouched children retain their stored data and depths.
  The binary proof needs no shape, packing-layout, alignment, clone, map, or
  termination laws. The progressive proof derives the actual layer-depth
  correspondence from successful checked arithmetic, without capacity,
  density, packing, or correctness laws for range/maximum answers.
  `ProgressiveList/ApplyUpdates/Caches.lean` covers every returned public state,
  including empty no-ops and restored errors. `Tree/HashCache/Validity.lean`
  defines a cache as zero or equal to a mathematical reference hash of its
  logical input; this is a specification predicate, not a replacement model
  of the unextracted Rust hash computation. `ApplyUpdates/CacheTotal.lean`
  combines cache validity with the complete public total specification.
- `Tree/PackedLeaf/PushState.lean` proves exact successful append contents,
  cache invalidation, full-leaf rejection, and complete state restoration for
  every returned push error. The underlying Rust push now invalidates an
  already populated cache (`63321b0`); see Rust corrections below.
  `Tree/PackedLeaf/Caches.lean` proves every returned mutable insertion clears
  the cache, including its bounds-error state, and every successful owning
  insertion clears it. The actual bulk-update loop retains its initial hash
  or clears it; a public packed update supplied with zero therefore returns
  zero, independently of old cache contents and clone behavior. These are
  operational prerequisites used by the binary/progressive/public bulk-update
  cache-preservation chain described above.
- `Tree/HashCache.lean` and `Tree/ProgressiveTree/HashCache.lean` describe
  cache predicates by leaf value, packed sequence, binary depth/sequence, or
  progressive depth/suffix. This retains padding and layer context and imposes
  no particular hash function or collision axiom. Predicates may accept the
  all-zero sentinel. `Tree/Rebase/CacheAction.lean`, `Caches.lean`, and the
  progressive/public list `Rebase/Caches.lean` modules prove invariant
  preservation through the actual rebase operations. Rebuilt nodes retain
  caches over unchanged child contents; whole-base binary replacements import
  the base's caches. Original progressive caches remain valid over unchanged
  suffixes, without a premise on base progressive caches. This is a proved
  preservation contract. Constructor initialization and extracted mutation
  preservation are now supplied above; semantic hash computation and shared
  cache writes remain outstanding.
- `Tree/ProgressiveList/TreeHash/Metadata.lean`: the actual trait classifies
  progressive lists as lists and unconditionally rejects both packing methods.
  These three specifications have no element, map, or structural premises.
  Root hashing and its shared cache effects remain outside the proof boundary.
- `Tree/Arbitrary/Models.lean`, `Generation.lean`, and `Reflection.lean`:
  the pinned arbitrary 1.4.1 vector protocol consumes a control byte before
  each element, stops on false or the first element error, and preserves the
  exact remaining input. Finite control/element traces imply termination with
  exact values, and every successful collection has such a trace. Vector
  capacity follows from the resulting or successful-prefix vector. Custom
  generators may replace their input; there is no artificial fuel, byte-length
  termination premise, or element-size-hint assumption.
- `Tree/ProgressiveList/Arbitrary/Behavior.lean` and `Generated.lean`:
  every successful extracted list generator stores the actual element-call
  sequence and its exact recorded length with dense, representable backing.
  Indexed representation and no pending updates require only the relevant
  empty-default-map laws. Vector and constructor errors retain exact input
  state and Rust error mapping, with no packing or map laws on error branches.
- `Tree/ProgressiveList/Arbitrary/Total.lean` and `Traits.lean`: constructor
  totality composes with the external trace to establish successful generation
  and full representation. Occupied-layer capacity is necessary and sufficient
  for success under a terminating default map. The actual owning-input default
  runs ordinary generation and discards its final input; both size-hint methods
  return their pinned defaults without element or map assumptions.
- `Tree/PackedLeaf/Insert.lean` proves necessary and sufficient position and
  vector bounds for insertion. `PackedLeaf/BulkUpdateSuccess.lean` proves
  actual vector cloning and the dense window scan terminate with the exact
  target length and merged indexed contents. All copied storage needs
  terminating clones; identity is required only for retained stored slots and
  pending values in the packing window. The original global-clone content
  interfaces remain specializations. `Tree/Vec/Clone.lean` recovers actual
  element results from successful vector cloning and proves lookup preservation
  from identity only at that slot. Its finite-list helpers characterize ordered
  cloning success by successful clones of the input values and derive unchanged
  output under identity cloning restricted to those values.
  `PackedLeaf/BulkUpdate.lean` uses these facts
  to prove a successful update preserves a queried slot without identity for
  unrelated values or for storage replaced by its pending value.
- `Tree/BulkUpdate.lean` now derives an unpacked leaf's actual pending lookup
  and stored clone directly from successful execution, without clone laws.
  Its existing value and extracted-lookup lemmas require clone identity only
  for the pending value at the checked `prefix + offset` key.
  `Tree/BulkUpdate/Contents.lean` uses the scoped packed-leaf theorem in its
  offset bridge, restricting clone identity to retained stored slots and the
  pending update window.
- `Tree/BulkUpdate/CloneScope.lean`: `BulkCloneScope` separates storage and
  pending-value laws in children selected by positive range queries. Skipped
  subtrees require no clone law, and zero expansion contributes no storage.
  It contains input data and external map observations only, with no assumed
  bulk-update result or recursive success. `BulkCloneOn` specializes it to
  termination on every copied value; `BulkRetainedCloneOn` restricts content
  laws to retained stored slots and selected pending values. `BulkCloneLaws`
  supplies stored termination and surviving-value identity for total content
  correctness. Projection, implication, and zero-expansion lemmas support both
  binary inductions and all six public contents, lookup, success, density,
  and total specifications. All four progressive-layer bridges carry the
  retained-slot law.
- `Tree/ProgressiveTree/BulkUpdate/CloneScope.lean` defines selected layers
  from checked geometry, range answers, and the actual maximum-index guard.
  A zero layer with no updates stops traversal; an existing node may skip its
  binary layer and still select its suffix. Its clone-input law combines these
  visits with the binary scope and contains no assumed bulk-update result.
  Both progressive contents and termination inductions now carry this scope
  through every left/suffix call. All six public list apply-updates contents,
  combined correctness, success, totality, and capacity-equivalence interfaces
  require cloning laws only within that scope for the maximum actually read.
  Complete public application retains its nonempty-branch guard. The total
  clone laws project to the separate termination and retained-value premises;
  no public content or total specification requires identity of discarded
  stored copies.
- `Tree/BulkUpdate/RangeScope.lean` describes both immediate child queries at
  each binary node and deeper queries only below positive answers. Leaf
  updates have no range-query requirement; zero expansion uses the same
  query geometry. `ProgressiveTree/BulkUpdate/RangeScope.lean` adds each
  reached nonempty layer window, its selected binary queries, and suffix
  queries guarded by the actual range answers and maximum. These relations
  contain no own-operation result or recursive-success premise. `BulkRangeOn`
  restricts an external law to those ranges. Both success inductions and all
  public apply-updates success/total/capacity specifications use it for
  range-query termination, with the public scope tied to the actual maximum.
  `UpdateMap/Range.lean` defines `RangeExcludesValuesAt` and
  `RangeReflectsValuesAt` for one endpoint pair and proves local reflection
  implies exclusion. Both query scopes lift that implication. The content,
  density, and success recursions and all eight public list specifications
  now restrict answer correctness to the same reached queries. Skipped
  descendants require no range law. The saturated empty-window helper asks
  for exclusion only when its wrapper queries a nonempty range, and the empty
  public total branch still needs no query law.
- `Tree/BulkUpdate/Arithmetic.lean` and `Success.lean` derive every binary
  split operation from the aligned endpoint bound and prove total recursive
  reconstruction, density, and merged contents. Zero expansion and unchanged
  shared children are covered. `ProgressiveTree/BulkUpdate/Success.lean`
  derives future visited-layer bounds from the final occupied length and
  proves the actual progressive spine recursion succeeds.
- `Tree/ProgressiveList/ApplyUpdates/Total.lean` and `Capacity.lean` connect
  these helpers to the public mutation. No successful rebuilding operation,
  input-map lookup, no-gap property, or independently bounded maximum is
  assumed. Final occupied capacity is both necessary and sufficient for
  nonempty application under the stated external laws. Empty application
  requires none of the rebuilding laws.
- `Tree/ProgressiveTree/Builder/ExtendSuccess.lean` and
  `ProgressiveTree/ConstructionTotal.lean`: finite iterator consumption and
  both progressive-tree constructors now have total sequence, length, density,
  and capacity specifications. Final occupied-layer representability supplies
  every intermediate rollover check; the actual new/push/finish bodies are
  composed with the proved iterator trace.
- `Tree/ProgressiveList/Construction/Total.lean` and `Capacity.lean`: iterator
  and vector construction, `TryFrom<Vec<T>>`, and SSZ `TryFromIter` succeed
  with the exact input representation, valid backing/spine, and no pending
  updates. The sequence capacity condition is necessary as well as sufficient
  for success, without a bound on the next unused layer. Map read/empty laws
  are needed for indexed/pending semantics, not for the success criterion.
- `Tree/ProgressiveList/PopFront/BuilderTotal.lean` and `Total.lean`: actual
  suffix streaming and front removal terminate and rebuild exactly the
  retained sequence. Only retained values need clone identity and capacity;
  clone, capacity, and default-map laws are conditional on a nonzero removal.
  No input iterator or successful builder result is exposed as a premise of
  the public front-removal specification.
- `Tree/Ssz/VariablePrefix.lean` and `PrefixRead.lean`: arbitrary complete
  variable prefixes compose with any remaining cursor behavior. Raw offset
  table and payload suffixes determine each actual step. Only the largest
  consumed offset needs an explicit 32-bit bound; all intermediate offsets,
  indices, slices, and builder bounds are derived internally.
- `Tree/Ssz/VariablePrefixErrors.lean`, `VariableElementErrors.lean`, and
  their public `ProgressiveList/Decode` counterparts: malformed next offsets
  retain fixed-section, bounds, then decreasing-offset precedence after any
  successful prefix. Nonfinal payload errors follow their boundary checks;
  final payload errors consume the complete remainder, including empty
  payloads. No parser or builder result is assumed by the public specifications.
- `Tree/Ssz/PayloadTrace.lean` and `ProgressiveList/Decode/PayloadErrors.lean`:
  proof-level annotations record each value's actual consumed bytes and erase
  back to the original decoder trace, including its stopping error. The five
  public error specifications cover fixed and variable prefixes without an
  encoding function or canonical-decoding law. Distinct encodings of equal
  values are supported; element laws concern only consumed payloads.
- `Tree/Ssz/VariableErrors.lean`: all variable item rejection branches return
  their exact error and preserve the current payload offset. Read failure,
  offsets into the fixed section, input bounds, decreasing offsets, and final
  byte bounds are covered with Rust's check order. `DecodedLength.lean` bounds
  any variable decoded prefix by the remaining table entries independently of
  element behavior, offset order, or canonical bytes. `FixedPrefix.lean`
  composes complete fixed encodings with a suffix's exact stopping behavior.
- `Tree/ProgressiveList/Decode/InitialErrors.lean`, `FixedErrors.lean`, and
  `VariableErrors.lean`: public error specifications derive actual cursor calls
  from byte layouts and element laws only on consumed payloads. First-offset
  rejection bypasses construction. Later errors finalize the partial builder,
  including initializing its default update map. `ErrorResult.lean` proves
  this finalization and public error propagation from arbitrary actual cursor
  traces; the fixed branch constrains only capacities occupied by successful
  prefix values, while variable capacity follows from the table size. No
  result of a milhouse builder or list operation is assumed.
- `Tree/ProgressiveList/Encode/Length.lean`: complete payload-size accumulation
  over the proved merged iterator. The fixed branch returns declared element
  width times represented length without traversal; the variable branch adds
  one four-byte offset per element to the sum of represented element sizes.
  Element size laws concern only consumed values, and one aggregate bound
  supplies all arithmetic bounds.
- `Tree/ProgressiveList/Encode/LengthCalls.lean`: the actual size loop equals
  the ordered fold of element size calls and checked additions. The public
  variable-size equation retains the final offset-table multiplication and
  addition after that fold. It assumes no element-size law or byte bound and
  preserves failure/divergence order, including overflow before later element
  calls. The existing sum specification describes successful fitting results.
- `Tree/ProgressiveList/Encode/FixedCalls.lean`: the actual fixed-element loop
  equals an ordered fold of element append calls, passing each returned buffer
  to the next call and preserving failure or divergence. Public `ssz_append`
  and `as_ssz_bytes` retain their actual length, multiplication, and reservation
  checks before this fold. These equations need no codec law, byte bound, or
  agreement between declared width and emitted payload sizes. The public
  equations use the represented sequence and its traversal invariants.
- `Tree/ProgressiveList/Encode/VariableCalls.lean`: the variable loop folds
  actual encoder append calls over the iterator sequence, threading returned
  encoder states and composing borrowed continuations in the actual order.
  Public `ssz_append` and `as_ssz_bytes` retain their reservation and
  finalization calls and continuation releases. These equations impose no
  codec law or byte/offset bound and preserve failure and divergence. The
  public equations derive iteration from represented contents and traversal
  invariants; they do not assume an iterator result or successful encoder call.
- `Tree/ProgressiveList/Encode/Fixed.lean`, `VariableLoop.lean`, `Variable.lean`,
  `Owning.lean`, and `Metadata.lean`: exact SSZ bytes through all actual encoding
  methods, including pending replacements/extensions and nonempty destination
  prefixes. Variable encoding writes offsets relative to the beginning of the
  encoded list, followed by the payloads in iterator order. Encoder continuation
  composition and final borrowed-buffer release are proved. `as_ssz_bytes`
  delegates to the proved append body with an empty vector, without cloning or
  a separate length pass. Fixed encoding has separate bounds for declared
  reservation and actual payload size, with no width-coherence premise.
  Its append laws apply only at actual sequence positions, on the initial
  prefix followed by preceding payloads. The owning encoder starts from an
  empty prefix. The fixed roundtrip retains width coherence to identify the
  decoder's chunks, derives the encoder payload bound from it, and uses the
  same restricted append law. Variable encoding and its roundtrip restrict
  append behavior to the temporary payload accumulated from preceding sequence
  positions. Its element calls do not receive the destination prefix or the
  offset table, and no behavior is required on those unrelated buffers.
- `Tree/Ssz/Models.lean`, `Bytes.lean`, and `Encoder.lean`: concrete external
  models for ethereum_ssz 0.10.0 and specifications of its offset writes,
  accumulation, and finalization. `offsetBytes` gives the canonical four-byte
  little-endian encoding, `offsets` advances by preceding payload lengths, and
  `variableEncoding` concatenates the table and payload. `OffsetsFit` constrains
  only offsets actually written, without a 32-bit bound on the final payload's
  end. Allocation/capacity is erased consistently with the existing vector
  abstraction, while logical size overflow is checked. The external offset
  writer models the development-profile assertion; the successful encoding
  proofs use fitting offsets, whose bytes agree in both debug and release.
- `Tree/Invariants.lean`, `Tree/Builder.lean`, `Tree/Roundtrip.lean`,
  `Tree/Rebase.lean`: binary-tree density, builder invariants, leaf-update
  read-back, and rebase shape preservation. Content preservation must be proved
  separately where the existing result establishes only density.
- `Tree/Rebase/Density.lean`, `Steps.lean`, and `Lengths.lean`: positional
  mixtures have lengths bounded by their two dense inputs; preserving the
  original length therefore preserves its dense prefix even when the base has
  a different length. Actual recursive rebase actions split length metadata
  correctly, preserve materialized length, and certify equal input lengths
  when returning an equality action. Binary rebase density no longer requires
  equally long inputs. These structural results need no element-equality or
  hash-collision law; the operational length and density proofs use the
  existing trusted `Arc.ptr_eq_spec` model law. Content preservation is proved
  separately under the semantic laws below.
- `Tree/Rebase/ContentsAction.lean`, `Contents.lean`: positive Rust vector
  equality implies exact contents equality under soundness of false element
  `ne`; the pinned generic slice loop calls `ne`, not `eq`. Unpacked leaf
  rebasing additionally needs soundness of true element `eq`. Neither result
  assumes termination, completeness, or reflexivity. The actual binary
  rebase action preserves contents, and equality actions also certify agreement
  with the base. `CachedHashesAgree` states an input cache law at corresponding
  nodes: equal nonzero hashes imply equal contents when materialized lengths
  agree. It imposes no constraint on zero caches or different-length sequences,
  and contains no rebase call or result. Connecting it to semantic hashing and
  maintained cache validity remains a separate hashing obligation and also
  needs an appropriate collision-soundness condition; valid cached hashes
  alone do not imply equal contents.
- `Tree/ProgressiveTree/Rebase/Steps.lean`, `Geometry.lean`, `Density.lean`,
  and `Contents.lean`: actual successful recursive calls either retain the
  original tree or rebuild from the binary action and recursive suffix. The
  calculated layer lengths match the dense materialized prefixes. Progressive
  rebasing preserves density and representable capacities with no equality,
  hash, or clone laws; only the original tree needs capacity bounds. Exact
  contents preservation adds true-`eq` and false-`ne` soundness and cache agreement
  for compared binary layers; unused progressive-node hashes need no law.
- `Tree/UpdateMap/Length/Equivalence.lean` characterizes complete length-result
  equality directly from raw maximum-query outcomes. Successful maxima must
  describe the same mathematical extent; errors and divergence agree, with
  the overflowing `usize::MAX` successor also matching an explicit integer
  overflow failure. `None` and `Some index` agree exactly when the index lies
  below the backing length. The public `len_with_updates_eq_iff_max_index`
  inherits this criterion without map validity or query-success premises.
  `Rebase/State.lean` proves the corresponding length/pending-observer laws
  necessary and sufficient and weakens `rebase_preserves_observers` from exact
  maximum identity to this relation. Emptiness-query equality is still exact;
  read, representation, element, and cache laws are unnecessary for these
  observers.
- `Tree/UpdateMap/Lookup.lean` and `ProgressiveList/Lookup.lean`: the raw lookup
  relation is necessary and sufficient for public reads to agree after
  replacing the pending map. Missing and present entries may agree when the
  actual backing lookup supplies the same value. Failure and divergence remain
  observable, and the exact map-read law implies the new relation. Every
  machine index is covered, including out-of-bounds reads; no structural or
  successful-query premise is assumed.
- `Tree/ProgressiveList/Clone/Maximum.lean`: under lookup agreement after the
  backing fallback, replacing the map preserves the represented sequence exactly when its
  returned maximum gives the same mathematical logical length: backing length
  for `None`, or `max (index + 1) backing_length` for `Some index`. The represented
  source length supplies the successor bound; neither exact maximum identity
  nor a successful new list-length call is assumed. Clone, clone_from, and
  dependent rebase sequence/cache contracts now use this weaker condition.
  `represents_with_updates_iff` also proves the lookup and maximum conditions
  jointly necessary and sufficient for complete sequence preservation, without
  an assumed read law. The length proof reuses `updated_length_eq_ok_iff`.
- `Tree/ProgressiveList/Clone/From.lean`: the actual public trait default and
  extraction-only caller agree. The default performs the source list clone;
  success is exactly source pending-map clone success. Successful and total
  source-sequence replacement preserve source backing invariants and exact
  backing fields, with no old-destination condition. Source cache predicates
  and the pending observer transfer under their own relevant premises. The
  source map's `clone_from` is never invoked, and no element clone law is added.
  `clone_from_success_represents_iff` characterizes successful source-sequence
  replacement by the actual source-map clone and its lookup/extent outcomes.
- `Tree/ProgressiveList/Clone/Total.lean`: list-clone success is equivalent to
  pending-map clone success, without representation or generic element laws.
  `clone_success_represents_iff` adds the exact lookup and maximum conditions
  to characterize successful sequence-preserving cloning. A terminating map
  clone preserving reads after the backing fallback and logical extent gives
  actual list termination, complete sequence and backing validity, unchanged tree and
  recorded length, and exactly that cloned pending map. The total contract
  assumes no own-method success, map/maximum identity, element cloning, or
  packing law. Raw map reads may differ when the backing lookup supplies the
  same value; maximum metadata may differ when the backing length dominates.
- `Tree/ProgressiveList/Clone.lean`, `Rebase/State.lean`: exact derived-clone
  state, sequence and backing preservation under the relevant pending-map
  clone laws, exact rebase success calls, and complete error restoration.
  In-place rebase preserves backing length, pending-map identity, logical
  length, and pending observers on every returned result. These frame and
  error results do not require a tree-content theorem. `Rebase/Backing.lean`
  lifts full backing preservation through both list methods without clone
  laws. `Rebase/Contents.lean` proves successful `rebase_on_spec` and
  `rebase_spec`, preserving represented contents and backing validity under
  the semantic equality/cache premises above. In-place rebasing needs no map
  laws; nonmutating rebasing adds only pending-map clone lookup agreement after
  the original backing fallback and matching logical extent.
  The general `Represents.with_tree` lemma preserves the pending overlay when
  valid backing trees have the same materialized sequence.
- `Tree/Rebase/Arithmetic.lean`, `Comparisons.lean`, `Success.lean`: actual
  length minimization and clamped child-length splitting always succeed within
  the checked shift bound. Binary rebasing succeeds for compatible shapes and
  sufficient routing depth, with that shift bound needed only when lengths
  are supplied. Recorded lengths need not equal materialized lengths for
  termination. Element `eq`/`ne` success is scoped to corresponding leaf pairs;
  pointer-equal leaves and different-length packed vectors need no element
  calls. No density, packing queries, cloning, or hash law is used for binary
  success.
- `Tree/ProgressiveTree/Rebase/Success.lean`: corresponding-layer comparison
  termination and compatible shapes imply recursive and public progressive
  success. Packing layout and representable original layers supply successful
  depth advancement, capacity calculations, saturating subtraction, minimum,
  full-depth addition, and both recursive calls. The base needs no capacity
  bound; either zero suffix ends traversal without element calls.
- `Tree/ProgressiveList/Rebase/Total.lean`: both public operations have actual
  success specifications under shape and capacity invariants, and total
  content/backing specifications combining that success with the existing
  semantic equality/cache laws. In-place rebasing preserves exact pending-map
  identity. Nonmutating rebasing returns precisely the pending-map clone and
  keeps the backing length; representation preservation adds only that
  clone's read/extent laws. The additional `Rebase/State.lean` lemmas prove
  these metadata facts on every successful nonmutating call without tree
  invariants, and preserve length/pending observers under only the clone laws
  relevant to those observers.
- `Tree/Arc/Equality.lean`, `Tree/Equality/Comparisons.lean`: faithful Arc
  comparison shortcuts and vector inequality foundations. The local external
  Arc model preserves the pinned triomphe implementation's pointer check, and
  `milhouse_models.vec_eq` negates the existing vector `ne` model to match Rust
  without an unstated element `eq`/`ne` coherence law. These corrections and
  extraction workarounds are recorded in UPSTREAM_BUGS issues 5, 12, and 17.
- `Tree/Equality/Inputs.lean`: `NeSpecAt` supplies termination and correctness
  for one actual element pair; `NeSoundAt` supplies only soundness of a false
  result. `NeOn` carries either law through the packed comparison prefix,
  demanding the suffix only after the preceding actual `ne` returns false.
  Uniform laws establish these scopes, and pointwise implication weakens them.
- `Tree/Equality/{Structure,Scope,Correctness,Soundness,Lookup}.lean` and
  `Tree/ProgressiveTree/Equality/{Structure,Scope,Correctness,Soundness,Lookup}.lean`:
  structure ignores hash caches but retains variants, zero depths, and values.
  Structural equality preserves materialized contents, density, and progressive
  capacity bounds. Actual recursive comparisons terminate and characterize
  this relation under input-scoped `NeSpecAt`; positive-result soundness needs
  only input-scoped `NeSoundAt`, without totality or completeness. Element laws
  stop at pointer sharing, mismatched variants, unequal packed lengths, and
  the first differing field or packed element. Plain and Arc comparison scopes
  distinguish the actual outer pointer check. `ElementSoundness.lean` proves
  the Arc/vector positive-result bridges using those scopes. No packing,
  density, cloning, or hash-content law is required by comparison correctness.
  Structural equality also preserves the complete extracted lookup computation,
  including errors and divergence, without layout, density, or bounds laws.
- `Tree/ProgressiveList/Equality/{Structure,Correctness,Pointer}.lean`: list equality
  combines the proved progressive comparison, exact recorded length, and an
  explicit map relation that permits different internal cache states. The
  unconditional positive-result characterization derives the three actual
  successful comparisons. `partial_eq_represents` transfers represented
  contents and backing validity under only successful-comparison soundness
  and map read/max agreement; the other backing invariant is derived. Direct
  backing and merged lookup congruence remove the layout premise from this
  result, and pure representation transfer needs no backing invariant. The
  total `partial_eq_spec` and `partial_ne_spec` require the map law only for
  the actual pair when tree structure and recorded length agree. All operational
  contracts inherit the backing tree's input scope instead of a global element
  law. With shared backing, the actual comparison rejects unequal recorded
  lengths or returns the negation of pending-map `ne`, preserving its failure
  and divergence without element, map, or representation laws.
- `Tree/Contents.lean`: a dense binary tree's materialized sequence has its
  recorded length, and extracted indexed lookup returns exactly that sequence's
  element. The pure slot theorem requires no packing laws or machine bounds;
  the extracted lookup bridge adds only the packing layout and routing shift
  bound. Wrapping modulo capacity is explicit. This supplies a content bridge
  for constructor and iteration proofs. Binary-builder sequence preservation
  is established by the separate results below.
- `Tree/Iter/Stack.lean`, `Path.lean`, `Path/Contents.lean`,
  `Path/Backtrack.lean`: exact saturating stack truncation; root-to-current
  search paths with the actual routing bits; current-frame depth and root-slot
  correspondence; path preservation through truncation, high-bit agreement,
  within-chunk advancement, and trailing-zero backtracking. Backtracking retains
  an ancestor while the next index remains inside the root capacity.
- `Tree/Iter/Construction.lean`, `Leaf.lean`: extracted binary iterator
  construction succeeds with the supplied root, starting index, length, and
  packing configuration, and establishes the cursor invariant without density
  or starting-index bounds. Exhaustion returns unchanged `none`. For a live
  valid cursor ending at an unpacked leaf, extracted `next` returns the root
  sequence's indexed value, increments once, and preserves the entire cursor
  invariant. Pop-and-restore and all count arithmetic are derived internally.
- `Tree/Iter/Packed.lean`, `Node.lean`, `Next.lean`, `Contents.lean`: packed
  leaves preserve the cursor both inside chunks and at boundaries; chunk
  divisibility supplies the checked subtraction and cast bounds. Node descent
  preserves the selected search path, unchanged index, and pending `next`
  result while reducing the remaining search depth. Every live `next` call
  terminates, returns the root sequence's indexed value, advances once, and
  preserves the invariant. Constructed binary iterators therefore enumerate
  exactly `root.elements.drop index`, including empty and out-of-range suffixes,
  before returning `none`. Premises are the actual packing laws, input-tree
  density, and the routing shift bound; the progressive layer-capacity proofs
  supply that bound when this result is applied to progressive traversal.
  No iterator-output, successful-call, or termination premise is assumed.
- `Tree/Iterator.lean`, `Tree/Iter/Contents.lean`: the stronger `IteratorDrains`
  relation proves binary enumeration ends in a state whose `next` returns
  unchanged `none`. This derives stable exhaustion for consumers that keep
  reading the backing iterator while handling pending extensions; no fused
  behavior is assumed of arbitrary input iterators.
- `Tree/ProgressiveTree/Iter/Layer.lean`, `Enter.lean`, `Cursor.lean`,
  `Advance.lean`, `Step.lean`, `Next.lean`, `Seek.lean`, and `Construction.lean`:
  density determines exact layer lengths and suffix drops; opening a layer
  supplies its proved binary iterator. Progressive advancement strictly
  decreases the pending spine, and complete `next` terminates, returns the
  represented head, and preserves the tail invariant even after exhaustion.
  Seeking and construction establish this invariant for every machine starting
  index, including past-end indices. Actual progressive `iter_from` enumerates
  exactly `root.elements.drop index`. Empty internal layers are included.
- `Tree/ProgressiveList/Iter/Overlay.lean`, `Cursor.lean`, `Next.lean`,
  `Construction.lean`, and `Length.lean`: represented reads supply the complete
  pending/backing overlay law, without extra map-read assumptions. The public
  iterator constructors establish exact merged-suffix enumeration, bounds
  behavior, and a cursor preserved by every live `next`. Both size observers
  return the remaining sequence length. `Iter/Traits.lean` extends complete
  merged-sequence enumeration to the actual borrowed `IntoIterator` method.
  `Tree/ProgressiveList/ToVec/Loop.lean` equates collection from a proved finite
  iterator with ordered element cloning followed by accumulator append. It
  preserves actual changed clone values, failures, and divergence.
  `ToVec/Clones.lean` lifts that equation through the public trait bridge and
  exact-length result, deriving initial allocation and all vector-push bounds.
  `ToVec/Total.lean` proves success exactly when clones of represented values
  succeed, returning their actual results in order with unchanged length.
  `ToVec.lean` derives the original loop and public exact-contents contracts
  from these generalized results under identity cloning of consumed values.
  These public results use dense, representable backing layers. Constructors
  supply these properties through builder finalization. `Backing.lean` names
  the combined invariant `BackingValid`, establishes it for empty/default/vector
  construction, and proves preservation by pending append and every mutable or
  CoW write-back without extra map or clone laws. `ApplyUpdates/Backing.lean`,
  `PopFront/Contents.lean`, and `Rebase/Backing.lean` preserve it through the
  extracted backing-changing list operations. Remaining trait and CoW bridges
  must connect their actual calls to these established invariants.
- `Tree/ProgressiveList/IterCow/Construction.lean`: actual CoW constructors
  establish the correct backing suffix and pending overlay, preserve pending
  state, and derive the logical-length bound from representation. Public
  starts accept the end and reject oversized indices with the exact bounds
  error. `IterCow/State.lean` proves exact successful state, unchanged-release
  restoration, restoration through every returned bounds error, and backing
  validity under arbitrary constructor continuation inputs. These state results
  require no representation, packing, or map-law assumptions; backing
  preservation needs only the input backing invariant. Complete CoW stepping
  and handle-method proofs still
  require their actual Rust extraction, as documented in UPSTREAM_BUGS.md.
- `Tree/ProgressiveList/PopFront/Builder.lean`, `State.lean`, and `Contents.lean`:
  the concrete streaming helper appends the proved iterator suffix and preserves
  the progressive builder invariant. The public operation's successful result
  represents exactly the sequence with its prefix removed and has a dense, representable
  backing tree; nonzero removals clear pending updates. Zero removal is an
  unconditional no-op, oversized removal reports the exact error, and every
  returned Rust error preserves the original list. Clone identity is restricted
  to retained values; backing validity requires no clone or map laws.
- `Tree/TrailingZeros.lean`: the exact positive-word trailing-zero valuation,
  shared by builder carry proofs and iterator backtracking.
- `Tree/Loop.lean`, `Tree/Builder/Contents/Basic.lean`, `Push.lean`,
  `Finish.lean`, and `Tree/Builder/Contents.lean`: partial-correctness loop
  induction and the complete binary builder push/finish content proofs.
  Successful `push` appends exactly one value and increments length once;
  successful `finish` preserves the complete pending forest, including packed
  partial leaves and zero padding. These preservation results require no
  density, packing, clone, arithmetic, or termination assumptions. The combined
  finalization theorem uses the existing builder invariant to supply density,
  the correct sequence length, and all routing bounds for exact indexed reads.
- `Tree/Builder/Carry.lean`, `Push/Loop.lean`, `Push/Success.lean`, and
  `Tree/PackedLeaf/Push.lean`: binary value insertion succeeds for every valid
  leaf-level builder with spare capacity, appends the supplied value, and
  preserves the invariant. The actual carry count is derived from the stack
  and trailing bits; packed leaf growth requires no cloning law.
  `Contents/Length.lean` identifies the logical counter with the complete
  stored sequence directly from validity.
- `Tree/Builder/Finish/PackedMerge.lean`, `Packed.lean`, `LevelMerge.lean`,
  `Step.lean`, `Loop.lean`, `Finalize.lean`, and `Success.lean`: every valid
  binary builder finishes successfully, including empty builders, partial
  packed leaves, zero padding, and nonzero-level builders. Packed-leaf
  finalization normalizes the forest, and each outer padding step strictly
  decreases the remaining capacity. Checked shifts, powers, additions, vector
  operations, and final singleton extraction are proved successful internally.
  `Builder.finish_total_spec` requires only `BuilderInvariant` and returns the
  exact stored sequence, depth, logical length, and dense root.
- `Tree/Iterator.lean`, `Tree/ProgressiveTree/Builder/Spine.lean`,
  `Contents.lean`, `Iterator.lean`, and `Tree/ProgressiveTree/Construction.lean`:
  exact subtree assembly order, empty progressive builder contents, successful
  append and length growth including rollover, counter preservation, finalization
  contents, and consumption of the complete input iterator sequence. Iterator
  output is defined by actual successful `next` calls through the first `none`;
  no fused-iterator law is imposed. The owning vector iterator satisfies this
  relation for its supplied vector without additional assumptions. Construction
  establishes all counter premises internally. The corresponding public list
  sequence results are in `Tree/ProgressiveList/Construction.lean`; the full
  indexed representation results are in `Construction/Representation.lean`.
- `Tree/ProgressiveTree/Density.lean` and `Builder/Density.lean`: progressive
  density implies shape, an adequate ending bound, exact materialized length,
  and mathematical slot/sequence agreement. Completed full layers occupy their
  precise geometric interval. Prepending them to a dense suffix preserves
  density, and actual spine assembly with a dense final layer produces a dense
  tree. These pure results add no packing or machine bounds.
- `Tree/Builder/Metadata.lean`, `Tree/ProgressiveTree/Builder/Invariant.lean`,
  `Finish.lean`: binary builder parameters remain fixed through push; successful
  progressive construction establishes the full-layer forest, correct current
  binary-builder depth and level, matching cached capacity, and exact counters.
  Every successful push preserves this invariant, including rollover, and every
  successful iterator loop preserves it without a separate finiteness premise.
  Finalization returns the same values and length in a dense bounded spine.
  The cached capacity formula is derived through both internal saturation stages
  and the final machine clamp in `Capacity.lean` and `Geometry.lean`.
- `Tree/ProgressiveTree/Builder/Bounds.lean`, `Push.lean`, `SpineSuccess.lean`,
  and `FinishSuccess.lean`: the complete layer geometry supplies counter
  agreement and guarantees room to increment total length. Progressive value
  insertion succeeds and preserves exact contents and validity; only a full
  current layer requires the next binary layer's capacity to be representable.
  This bound is needed because a fitting total counter alone does not ensure
  that a new power-of-two binary capacity fits. Spine assembly terminates with
  the exact subtree fold without shape or packing assumptions. Finalization
  succeeds from geometry alone; full validity additionally establishes the
  exact value sequence and recorded length, density, and representable layers.
- `Tree/ProgressiveTree/Bounds.lean`, `Lookup.lean`: representable layer
  capacities are preserved by assembly. From these bounds and packing layout,
  extracted lookup derives successful depth arithmetic, binary-depth conversion,
  layer endpoints, and routing shifts, and agrees with mathematical slots.
  Density then gives exact sequence indexing, including the missing suffix and
  saturating offsets for non-root suffixes. No independent routing bound or
  arithmetic-success hypothesis is required.
- `Tree/ProgressiveList/Construction/Representation.lean`: dense bounded backing
  trees with an empty pending map represent their materialized sequence. The
  public successful-constructor specifications establish exact indexed contents
  and logical length, `SpineValid`, and no pending updates. Only the packing,
  input-iterator, and empty-default-map laws remain as semantic premises; none
  assumes the builder's result or the desired lookup postcondition.
- `Tree/ProgressiveTree.lean`: exact routing to binary-tree lookups, plus
  selected-subtree density and update read-back lemmas.
- `Tree/ProgressiveTree/Capacity.lean`, `Depth.lean`, `Geometry.lean`: exact
  clamped geometric capacity at every depth, including internal `u128`
  saturation; checked progressive-to-binary depth conversion; monotonicity,
  leaf alignment, and exact adjacent layer windows when the binary capacity
  fits. A nonempty machine-index window has an unclamped start, so its offset
  alignment can be established before the binary update supplies its capacity
  bound. These modules are included through the root `Tree` import.
- `Tree/ProgressiveTree/BulkUpdate/Layer.lean`: a successful binary update in
  a nonempty progressive layer preserves shape and contents, with its exact
  width and alignment derived from the extracted capacity calculations.
  Read-back through the progressive node is proved both for existing layers
  and for expansion from zero. Sibling invariants and extra shift/window
  arithmetic assumptions are not required. The pending-override theorem derives
  old binary-read success from the update, avoiding a readability premise.
- `Tree/ProgressiveTree/BulkUpdate/Steps.lean`, `Range.lean`, `Contents.lean`:
  exact successful execution decomposition and the complete recursive
  shape/content theorem. The proof preserves the bound on where the spine ends
  and handles both maximum-index cutoffs and the zero early exit, including
  saturation. Only extension completeness, false-range exclusion, and the
  maximum's upper-bound law are required from the update domain and map.
- `Tree/ProgressiveList/ApplyUpdates/Contents.lean`: sequence representation
  implies extension completeness; successful `apply_updates` preserves that
  sequence at every index, with pending-value precedence and no separate
  backing-readability premise. `ProgressiveList/Spine.lean` establishes and
  preserves the backing geometry and ending bound for empty/default creation,
  push, and mutable write-back.
- `Tree/BulkUpdate/Window.lean`, `Tree/UpdateMap/Domain.lean`, and `Range.lean`:
  a global dense update domain restricts and splits into the exact subtree
  windows; empty windows retain their old lengths, and windows with updates
  have positive new lengths. Lookup membership follows from actual successful
  reads. Exact successful range answers supply both positive witnesses and
  the existing false-range exclusion law.
- `Tree/BulkUpdate/Density.lean`: successful binary bulk updates preserve the
  dense window length with nonzero global offsets, including packed leaves,
  transient zero expansion, and both node children. Successful arithmetic also
  supplies representable capacity. No clone-identity law is needed for density.
- `Tree/ProgressiveTree/BulkUpdate/Density.lean`: selected progressive layers
  retain their exact dense prefix; untouched layers, maximum-based suffix
  skips, and the zero early exit preserve density and capacity bounds. The
  complete recursive and public bulk-update specifications establish the new
  dense backing length and `Fits` from the old invariant and dense update
  domain, without independent alignment or arithmetic-success assumptions.
- `Tree/ProgressiveList/ApplyUpdates/Backing.lean`: representation establishes
  both extension completeness and boundedness of every pending value, giving
  the full dense update domain without an extra map law. Successful
  `apply_updates` preserves `BackingValid`; the combined public specification
  preserves the represented sequence and traversal invariant and clears pending
  updates. Density preservation needs no clone or default-map laws; contents
  and cleared updates use the corresponding laws separately.
- `Tree/ProgressiveList.lean`: pending/backing lookup behavior and push/read-back
  at all query indices, conditional only on the relevant insertion law.
- `Tree/Cow/Value.lean`, `Tree/UpdateMap/CopyOnWrite.lean`, and
  `Tree/ProgressiveList/CopyOnWrite/Fallback.lean`: extracted handle-data reads
  and unchanged release require map laws only at the actual selected fallback.
  `Contracts.lean` describes that selection using input lookups, independently
  of acquisition success; `Acquisition.lean` recovers it from actual execution
  and gives the exact lifted map result. `Conditions.lean` proves both scoped
  laws necessary and sufficient for the corresponding public behavior, without
  representation, clone, or termination assumptions. Unchanged release
  preserves every list field; arbitrary write-back preserves the backing spine.
  No bridge from the data observer to Rust `Deref` is assumed. The original
  stronger public signatures remain adapters in `CopyOnWrite.lean`.
- `Tree/Cow/Metadata.lean`: the extracted callback records the exact maximum,
  clears its action, and executes only once; attaching maximum-index tracking
  changes no carried value and unchanged release restores the original handle
  and metadata. Equivalent direct Rust metadata updates avoid built-in
  `Option::take` and `Ord::max` model mismatches. Full handle-method limitations
  and the supported extraction boundary are documented in `UPSTREAM_BUGS.md`.
- `Tree/ProgressiveList/WriteBack.lean`: lookup agreement after the actual
  backing fallback and maximum-result agreement are jointly necessary and
  sufficient for an in-bounds `List.set` result after replacing the pending
  map. No map law is assumed in this equivalence. The shared result is used by
  both mutable and consuming CoW continuation criteria and sequence proofs.
  `Lookup.lean` characterizes selected-value reads and replacement frames,
  including failure/divergence, without bounds or representation premises.
  `GetMutWithWriteReads` and `GetCowWithValueWriteReads` apply those raw lookup
  conditions to actual returned mutable and filled CoW continuations. Their
  adapters prove the old exact insertion/lookup laws sufficient for any backing
  function; the original stronger laws remain available.
- `Tree/ProgressiveList/Mutable/Fallback.lean` and `FallbackTotal.lean`: the exact
  pending-or-clone read equation preserves nonidentity clone results and
  failures. Present-element success needs termination of only the fallback
  clone that can actually be called. `get_mut_spec_of_fallback` composes that execution
  with exact sequence replacement and backing-field preservation;
  `get_mut_total_spec_of_fallback` covers every index, including missing-index restoration.
  All four map laws are restricted to the actual fallback dictionary and
  `(tree, length)` environment; unrelated fallback behavior is unconstrained.
  `Mutable.lean` and `Mutable/Total.lean` retain the older signatures as
  adapters from laws for every fallback. Law-independent state and exact
  write-back criteria live in `Mutable/State.lean`.
  Write/max-result agreement laws apply only in bounds, and the missing-handle
  law only out of bounds. Maximum metadata need only preserve logical extent
  at the original backing length, not record the exact insertion maximum.
  `len_after_get_mut_eq_iff_max_index` characterizes full length-result
  preservation from raw query outcomes without bounds or representation
  premises; `len_after_get_mut` drops its separate bounds premise.
  `get_after_get_mut_eq_iff_lookup` gives the exact public read criterion, and
  `get_mut_represents_set_iff` characterizes complete sequence replacement by
  lookup and maximum agreement. The sequence and total contracts use lookup
  agreement after the original backing fallback rather than raw map equality;
  the selected replacement may be supplied by that fallback.
  The older read-agreement lemmas now scope clone identity to the
  actual fallback instead of every value of the element type.
  `Mutable/Conditions.lean` additionally characterizes successful acquisition
  and its specified optional return value using only reached pending/backing
  reads and the actual clone result. No representation, backing invariant,
  write, metadata, or clone law is required upfront; the read law is local to
  this fallback. For an actually present immutable read, the fallback clone's
  termination is proved necessary as well as sufficient.
- `Tree/Cow/EntryModels.lean`, `EntrySuccess.lean`: external BTree/Vec vacant
  entries retain keyed exclusive-slot write-back state instead of `Unit`.
  Vector slots retain original backing length so the pinned growth calculation
  and vector-size checks are preserved. An index below the machine maximum
  supplies all arithmetic successes and the exact resulting backing length.
  Other keys and occupancy belong to the enclosing map continuation; allocation
  failure is abstracted as in the existing collection models.
- `Tree/Cow/Consuming.lean` and `ConsumingConditions.lean`: actual consuming
  success is equivalent to structural entry readiness and successful cloning
  only on an immutable branch. A specified initial value is characterized by
  the actual clone result or the existing mutable value. `EntryConditions.lean`
  proves the vector destination's successor bound necessary as well as
  sufficient in the local collection model; no entry-key equality is required.
  Every actual successful continuation has the `Written` entry/maximum-index
  footprint, without supplied readiness or clone laws. Missing entries reject
  without cloning or changing maximum metadata. Concrete inline Rust helpers
  and explicit result matches retain the supported consuming extraction;
  borrowed methods remain separate obligations.
- `Tree/UpdateMap/CowWriteBack.lean`,
  `Tree/ProgressiveList/CopyOnWrite/FallbackConsuming.lean`: structural
  entry readiness and cloning only for immutable returned handles compose
  with selected lookup/maximum agreement laws to prove complete in-bounds
  sequence replacement. `get_cow_into_mut_spec_of_materialization` derives
  the handle and every consuming subcall, preserving logical length and
  backing fields without entry-key equality, pending-handle classification,
  or a packing/backing invariant beyond indexed list representation.
  `Materialization.lean` proves these input conditions necessary and gives
  the exact acquisition-and-consumption success criterion under the read law.
  `get_cow_into_mut_writeback_spec` recovers the footprint from execution,
  without CoW read, entry-location, clone, or materialization-input assumptions.
  The older entry-location and absent-pending clone contracts remain adapters.
  The length equivalence gives the necessary-and-sufficient metadata criterion for every
  returned handle, without a write-footprint, bounds, representation, or
  successful-query premise. Its successful-length corollary needs no separate
  index bound. `UpdateMap/Mutable.lean` and `UpdateMap/CowWriteBack.lean` retain
  the old exact insertion laws and prove they imply the new contracts below
  an existing successful logical end.
  `get_after_cow_writeback_eq_iff_lookup` and
  `cow_writeback_represents_set_iff` give exact read and sequence criteria for
  returned continuations without write-law or filled-footprint assumptions.
  The sufficient sequence and consuming-total contracts use the weaker lookup
  law; actual `Written` entry/metadata effects and clone requirements are retained.
  `Deref`, borrowed `make_mut`, and CoW iterator stepping remain separate open
  obligations.
- `Tree/PackedLeaf/Contents.lean`, `Tree/PackedLeaf/BulkUpdate.lean`: exact
  packed insertion contents and bulk-update window contents, including initial
  cloning and the complete scan. Pending values override their own slots;
  absent updates preserve the previous values. No density or map metadata
  assumptions are needed for these successful-execution content results.
- `Tree/Arithmetic.lean`, `Tree/Shape.lean`: shared checked-arithmetic and
  routing lemmas, a geometric shape invariant derived from `DenseTree`, and
  exact correspondence between extracted lookup and mathematical slot contents.
  Shape admits transient nodes with two zero children without requiring density.
- `Tree/BulkUpdate.lean`, `Tree/BulkUpdate/Node.lean`,
  `Tree/BulkUpdate/Contents.lean`: unpacked-leaf contents, exact node-update
  decomposition, and the complete recursive shape/content theorem, including
  zero expansion and aligned global map offsets. The extracted-lookup corollary
  derives its shift bound from successful execution. Only false range answers
  must exclude pending values; density and positive-range completeness are not
  needed for this successful-execution content theorem. Its capacity bound is
  also exposed to the progressive-window proof.

## Validation

The 2026-09-09 scope revisions themselves changed documentation only. The
subsequent proof work is validated by the latest checkpoint below.

For each completed piece: build its Lean module, check the assumptions, and
commit with signing disabled and a model co-author trailer. Before completion:
regenerate the full extraction, build all proof modules, inspect axiom
dependencies for admissions, run the relevant Rust tests and formatting checks,
and audit every row above against concrete theorem statements.

For the complete current library axiom/import audit, run from the repository
root:

```sh
python3 scripts/aeneas-audit-axioms.py
```

The command builds first, inventories every public, private, and generated
theorem declaration from the Lean environment, and verifies that all `Tree`
library source modules are imported (excluding the two external templates).
It rejects unexpected axiom dependencies and axiom declarations, incomplete
inventories, and missing modules. The only permitted nonstandard axioms are
the two existing external contracts documented in `Tree/FunsExternal.lean`.
Command logs, the raw inventory, and a detailed JSON report are retained under
`aeneas-lean/.lake/axiom-audit/`. This gate checks axiom dependencies and module
coverage; model fidelity, API coverage, and theorem-hypothesis minimality still
require their separate audits.

For the available included API roots' local model dependencies, run:

```sh
python3 scripts/aeneas-audit-progressive-models.py
```

This separate gate builds first, follows elaborated definition-body references,
and checks the root inventory, generated root provenance, complete output, and
absence of selected incompatible local models. Its conservative dependency
closure includes unused dictionary fields and branches and does not resolve
abstract generic callbacks. See the [model audit](PROGRESSIVE_LIST_MODEL_AUDIT.md)
for the manifest, report, trusted boundaries, and remaining fidelity work.

The [2026-09-10 upstream version review](UPSTREAM_VERSION_REVIEW.md) identifies
relevant merged fixes and tests two newer releases in isolation. Both require
Slice model changes; latest also changes Result proof techniques. Fresh CoW
extraction checks await Rust nightly 2026-08-18. No tool pin, source, or proof
was changed, and no outstanding extraction obligation is discharged by this
review.

Latest MaxMap mutable-wrapper checkpoint (`fec41a5`): `get_mut_with`,
`get_cow_with`, and `get_cow_with_value` now extract and compile through
cfg-gated callers. Explicit Rust Option matches avoid the borrowed `Try`
signature mismatch; `handle` locals avoid a generated namespace collision.
The call order, early returns, metadata effects, and cloning behavior are
unchanged. UPSTREAM_BUGS issue 9 records the failed original probe, including
the failure when the actual Option helper source is included. Aeneas and the
external templates/models are unchanged; earlier generated function bodies
are unchanged. The extraction script also trims emitted trailing whitespace.

Eight public lemmas in `UpdateMap/MaxMap/Mutable.lean` prove the exact result,
complete continuation, initial-value correspondence, and success equivalence.
Present loans record the borrowed index without inner maximum, cloning,
cache-validity, or index-bound laws; missing loans preserve the cache for every
continuation input. Lookup frames transfer pointwise from the actual inner
loan, and missing-loan restoration transfers from that same inner invocation.
All eight proofs use only `propext` and `Quot.sound`.

The 324 Rust library tests pass with `arbitrary`; the eight update-map tests
were rechecked after the final namespace-safe local-name adjustment. Rustfmt
and the focused Lean build pass. The new CoW wrapper bodies are compiled,
but their correctness contracts are not yet proved. Further semantic-invariant
and concrete dictionary composition, borrowed CoW, and remaining assumption/
model-fidelity review stay open. Debug and Serde are excluded; TreeHash is
deferred.

The full build passes (2,162 jobs), and the complete axiom/import audit covers
6,207 theorem declarations across 446 project modules: 6,088 use only standard
Lean axioms or none, and 119 retain the existing Arc pointer contract. No new
nonstandard axiom dependencies are introduced. Logs are
`/tmp/milhouse-max-map-borrow-extraction.log`,
`/tmp/milhouse-max-map-mutable-axioms.log`,
`/tmp/milhouse-max-map-borrow-native.log`,
`/tmp/milhouse-max-map-borrow-native-final.log`, and
`/tmp/milhouse-max-map-borrow-full-audit.log`.

The model dependency audit passes for the unchanged 42 roots and 151 local
declarations (`/tmp/milhouse-max-map-borrow-model-audit.log`). All nine source
reports retain current input hashes and 52 checked proofs (20 axiom-free,
32 standard-only); their inputs are unchanged, so those suites were not rerun.

Previous MaxMap source checkpoint (`a5c77c3`, cache validity `72dba6d`): five
actual wrapper paths now extract through cfg-gated proof callers: default,
lookup, insertion, cardinality, and maximum. Eleven operational lemmas prove
exact delegation, result propagation, inner/wrapper success equivalence,
lookup frames, and cached insertion metadata. Six semantic lemmas specify
valid maxima, characterize valid default construction by the actual inner
outcome, and preserve validity through insertion. The invariant bounds
successful present reads and attains a present cache; it does not assume
all reads terminate. Exact cached insertion metadata is independent of that
invariant, inner maximum-query laws, cloning, and index/successor bounds.

All seventeen public lemmas pass individual axiom checks: five are axiom-free
and twelve use only standard Lean axioms. Full extraction succeeds, and the
eight existing `update_map::tests` pass with the arbitrary feature enabled.
Formatting passes for the added proof callers. Existing Rust method bodies,
prior extracted function bodies, external templates/models, and Aeneas are
unchanged. Concrete inner dictionary composition and the remaining MaxMap
mutable/CoW, range, and trait paths are still open, alongside borrowed CoW and
the remaining assumption/model-fidelity review. Debug and Serde remain
excluded; TreeHash remains deferred.

The full build passes (2,161 jobs). The complete axiom/import audit covers
6,190 theorem declarations across 445 project modules: 6,071 use only standard
axioms or none, and 119 retain the existing Arc pointer contract. It introduces
no new nonstandard axiom dependencies. Logs are
`/tmp/milhouse-max-map-extraction.log`,
`/tmp/milhouse-max-map-operations-axioms.log`,
`/tmp/milhouse-max-map-maximum-axioms.log`,
`/tmp/milhouse-max-map-native.log`, and
`/tmp/milhouse-max-map-full-audit.log`.

The model dependency gate also passes with the unchanged 42 roots and 151
local declarations (`/tmp/milhouse-max-map-model-audit.log`). SSZ and Arbitrary
source suites were rerun because their inputs include regenerated `Tree.Types`;
both pass. All nine source reports now have current input hashes and retain
52 checked proofs (20 axiom-free, 32 standard-only). The seven unaffected
suites were not rerun. Regression logs are
`/tmp/milhouse-max-map-ssz-regression.log` and
`/tmp/milhouse-max-map-arbitrary-regression.log`.

Previous VecMap source checkpoint (`ad39a6d`, invariants `235382e`): the pinned
0.8.2 map has seven exact source equations covering construction, count and
emptiness observers, indexed lookup, mutable lookup, and their actual Option
borrow helpers. Six additional contracts establish the count invariant,
connect observers to occupied slots, and specify and preserve mutable loans.
The thirteen standalone proofs use only standard Lean axioms or none; one is
axiom-free. Four native tests and four new provenance-validation tests pass.

All nine source suites pass with the shared runner's mixed-source-crate
validation. Their reports have current input hashes and contain 52 checked
proofs: 43 direct equations/comparisons, one parameterized comparison, two
compositions, and six derived VecMap contracts (20 axiom-free, 32 standard-only).
No production Rust, external model, main extraction, or Aeneas source changed.
The main `Tree` sources and 42-root/151-declaration inventory are unchanged;
their previous full build/axiom result remains 6,163 declarations across 443
modules and was not repeated for this standalone source-contract work.

The reproduced insertion probe fails on iterator `try_fold` signatures and
an erased region (UPSTREAM_BUGS 28). Concrete insertion/range/max operations,
entry footprints, and `UpdateMap`/`MaxMap` composition remain unfinished, along
with borrowed CoW and the remaining assumption/model-fidelity review. Debug
and Serde remain excluded; TreeHash remains deferred.

Previous consuming materialization checkpoint (`8bb4bb4`, list contracts
`477cdb3`): actual `Cow.into_mut` success is equivalent to structural entry
readiness and clone termination only for immutable handles. A specified
returned value is characterized by the actual clone result or existing mutable
value. The vector destination's successor bound is proved necessary from the
local entry model's growth arithmetic. Every actual successful continuation
has the filled-entry and maximum-index footprint without supplied entry or
clone laws.

For lists, `get_cow_into_mut_success_iff_of_fallback` requires only the selected
CoW read law upfront: success is equivalent to a present immutable read and
these materialization inputs for the returned handle. The complete
`get_cow_into_mut_spec_of_materialization` derives execution and represented
single-element replacement without entry-key equality or a pending-handle
classification law. `get_cow_into_mut_writeback_spec` recovers the footprint
from actual successful calls and needs no additional CoW read, location, or
clone laws. Older public contracts retain their signatures as adapters.

All ten new public lemmas pass individual axiom checks using only standard
Lean axioms. The full build passes (2,159 jobs), and the axiom/import audit
covers 6,163 declarations across 443 modules: 6,044 use only standard axioms
or none and 119 retain the existing Arc pointer contract. Logs are
`/tmp/milhouse-cow-materialization-axioms.log` and
`/tmp/milhouse-cow-materialization-full-audit.log`. No Rust, extraction,
external model, or Aeneas source changed. The eight source suites and unchanged
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Borrowed CoW and remaining assumption/model-fidelity work stay open;
Debug and Serde remain excluded and TreeHash remains deferred.

Previous CoW fallback checkpoint (`c7310ef`, exact criteria `5ad99dc`): eleven
weaker read, release, and consuming-write contracts require map laws only for
the fallback selected by actual input lookups. A pending hit selects `none`;
a miss selects the successful backing-read result. Selection is independent
of acquisition success and is recovered from actual successful execution.
All sixteen original public theorem names and signatures remain available.

Two law-independent execution lemmas recover the selection/continuation and
give the exact lifted map result, including failures and divergence.
`CopyOnWrite/Conditions.lean` additionally proves the selected-fallback read
and release laws necessary and sufficient for the corresponding public
behaviors. These equivalences impose no representation, clone, termination,
or structural assumptions. Consuming mutation retains the actual filled-entry
footprint and requires clone termination only when the value is absent from
pending updates; borrowed `Deref`, `make_mut`, and iterator stepping remain open.

All fifteen new public lemmas pass individual axiom checks using only standard
Lean axioms. The full build passes (2,156 jobs), and the axiom/import audit
covers 6,147 declarations across 440 modules: 6,028 use only standard axioms
or none, and 119 retain the existing Arc pointer contract. Logs are
`/tmp/milhouse-cow-fallback-axioms.log` and
`/tmp/milhouse-cow-fallback-conditions-full-audit.log`. No Rust, extraction,
external model, or Aeneas source changed; the eight source suites and unchanged
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Remaining assumption/model-fidelity review is separate. Debug and Serde
remain excluded, and TreeHash remains deferred outside the current goal.

Previous mutable fallback checkpoint (`06e66dc`, exact criteria `dfdc682`):
thirteen weaker theorems restrict read, write-read, maximum-result, and
missing-handle map laws to the actual fallback dictionary/environment supplied
by `get_mut`. The complete total specification preserves represented sequence
replacement, logical length, backing fields, and missing-index restoration.
All eighteen original theorem names and signatures remain available, with
stronger contracts delegated to the new proofs.

Three further equivalences characterize a successful specified optional
value, successful acquisition, and the exact clone-termination requirement
for an actually present immutable read. The general acquisition criteria
require only the read law for this fallback; they impose no representation,
structural backing, write, metadata, or clone law upfront. The pending,
missing-backing, and cloning cases are explicit and retain failure/divergence.

All sixteen new public lemmas pass individual axiom checks with only standard
Lean axioms. The full build and axiom/import audit pass for 6,130 declarations
across 434 modules: 6,011 use only standard axioms or none, and 119 retain the
existing Arc pointer contract. No Rust, extraction, external model, or Aeneas
source changed. The eight source suites and 42-root/151-declaration dependency
gate were not repeated for this proof-only change. Borrowed CoW and remaining
assumption/model-fidelity work stay open; Debug, Serde, and TreeHash remain
outside the goal.

Latest core adapter source-model checkpoint (`7b2939e`): axiom-free comparisons
validate the actual `Result::map_err`, `hint::must_use`, and blanket
`Borrow::borrow` bodies. The error adapter preserves arbitrary callback
success, failure, and divergence, without callback laws or termination
assumptions. The core suite passes seven comparisons and eleven native tests.
The full library build and axiom/import audit pass for the unchanged 6,103
declarations across 429 modules, with no new external axiom or admission.

No production Rust, local model body, main extraction, shared runner, or Aeneas
source changed. The other seven source suites and the dependency gate were
not repeated; their inputs are unchanged. The current source reports cover
36 direct comparisons, one parameterized comparison, and two compositions,
totaling 39 proofs (19 axiom-free, twenty standard-only). The model inventory
remains 42 roots and 151 local declarations. Borrowed CoW and other
model-fidelity obligations remain open; Debug, Serde, and TreeHash remain
outside the goal.

Latest power source-model checkpoint (`eb2f91b`): `core_pow_agrees` validates
the complete extracted `usize::pow` body for both compiler-selector outcomes,
including both loops, zero exponents, and overflow. Its axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. Four native tests and four
Python provenance/control-flow tests pass. All eight source suites pass:
33 direct comparisons, one parameterized source comparison, and two
compositions, totaling 36 proofs (16 axiom-free, twenty standard-only).

The full library build and axiom/import audit pass for 6,103 declarations
across 429 modules: 5,984 use only standard axioms or none, and 119 retain the
existing Arc pointer contract. The dependency gate passes for the unchanged
42 roots and 151 local model declarations. No production Rust, production
model, main extraction, or Aeneas source changed. The compiler-selector and
scalar foundations remain explicit; borrowed CoW and remaining model-fidelity
work are unfinished. Debug, Serde, and TreeHash remain out of scope.

Latest apply-updates binary selection necessity checkpoint:

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

Previous apply-updates skipped-binary materialization checkpoint:

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

Previous apply-updates binary density range checkpoint:

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

Previous apply-updates execution-guard checkpoint:

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

Previous apply-updates binary skipped-value checkpoint:

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

Previous apply-updates progressive/list clone-identity checkpoint:

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

Previous apply-updates binary clone-identity checkpoint:

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

Previous apply-updates query-termination checkpoint:

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

Previous apply-updates stored-clone checkpoint (`d3dbb3c`, progressive/list
necessity `5595942`, binary necessity `c9ca4f3`, scope/packed necessity
`5934163`): Focused and full builds pass (2,114 jobs). The axiom/import audit covers
5,794 declarations across 398 modules: 5,675 use only standard Lean axioms
or none, and 119 use the existing Arc pointer contract. All 13 new named lemmas
use standard Lean axioms; private/generated helpers are included in the inventory.
No new axiom or admission was introduced. External axiom use is unchanged, and
`size_of` remains unused. Existing success, total, and cache proofs validate.

Successful execution forces termination of all selected stored clones,
including copies later overwritten by updates. The packed proof covers any
returned Rust result and needs no metadata or input invariant. Binary necessity
needs layout and prefix alignment, with no shape, density, capacity, offset
alignment, range-correctness, lookup-termination, or clone law. Progressive
and public list necessity need only layout on the rebuilding branch. The total
clone law is exactly stored termination together with identity on retained slots
and selected pending values.

Four public existence criteria now assume only that retained/pending identity
law and put stored-clone termination on the necessary-and-sufficient side with
start, occupied capacity, positive selection, skipped-layer/suffix agreement,
and an actual default outcome. No successful update or stored-clone termination
is assumed upfront. The representation variants add exact default extent and
self-overlay; pending emptiness remains an independent observer law. The no-op
must already have valid backing storing the contents and has no rebuilding
clone requirement; its representation variant uses input representation.
Output backing validity is included, so stored-list equality alone is a weaker
observation.

Remaining retained-identity, binary range, query-termination, and geometry
minimality, borrowed CoW, and model fidelity are unfinished. No Rust, extraction,
external model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous apply-updates start-necessity checkpoint (`0f0b606`, progressive/list
necessity `ffe7dc6`, selected execution/shape `effb200`, binary necessity and
success equivalence `85703b8`, node selection `3d2a8b4`): focused and full library
builds pass (2,108 jobs). The axiom/import audit covers 5,770 declarations
across all 392 modules: 5,651 use only standard Lean axioms or none, and
119 additionally use the existing Arc pointer contract. All 16 new named
lemmas use standard Lean axioms or none; private/generated declarations are
included in the inventory. No new axiom or admission was introduced. External
axiom use is unchanged, and `size_of` remains unused.

The selected-layer start condition is now necessary as well as sufficient under
the remaining execution laws. A successful binary node must select a child;
positive range witnesses then supply its pending value. Packed terminals retain
the no-pending-entry exception. This necessity proof needs no false-answer,
clone, density, capacity, or termination law; it uses alignment, packing layout,
and packed-leaf metadata compatibility. Actual progressive success supplies a
successful binary call at every selected layer with no external or input
invariant laws. Input shape separately supplies metadata compatibility.

Four public existence criteria now place start conditions, occupied capacity,
positive selection, skipped-layer/suffix agreement, and actual default
construction on the necessary-and-sufficient side. No start condition or
successful update is assumed upfront. Final representation additionally needs
the default's exact extent and self-overlay; pending emptiness remains an
independent observer law. The no-op must already have valid backing storing the
contents, with input representation used by the representation variant.
Rebuilding assumptions apply only on the nonempty branch. Output backing
validity is included; equality of stored lists alone is a weaker observation.

Existing success, total, and cache contracts still validate. Remaining binary
range, clone, and geometry minimality, borrowed CoW, and model fidelity are
unfinished. No Rust, extraction, external model, or Aeneas source changed; the
seven source suites and 42-root/151-declaration dependency gate were not
repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
is deferred outside the goal.

Previous apply-updates start-condition checkpoint (`ded30f2`, nonempty existence
criteria `4063863`, total correctness `56bb004`, public execution `2915fca`,
progressive execution `13cac37`, progressive scope `9b286fc`, binary activation
`6650b5d`): focused and full library builds pass (2,103 jobs). The axiom/import
audit covers 5,730 declarations across all 387 modules: 5,611 use only standard
Lean axioms or none, and 119 additionally use the existing Arc pointer contract.
All 18 new named lemmas use standard Lean axioms or none; private/generated
declarations are included in the inventory. No new axiom or admission was
introduced. External axiom use is unchanged, and `size_of` remains unused.

Successful execution now follows from start conditions on selected progressive
layers, with binary reflection inside them and termination of reached queries
and selected clones. Packed terminals need no pending-value witness. Raw
execution requires neither positive progressive selection nor skipped-value
agreement. Adding those materialization conditions gives total correctness
with valid backing and preserved contents. Four new existence criteria cover
valid materialization, with or without final representation, on the rebuilding
branch and across both branches. They put occupied capacity, positive selection,
skipped-layer/suffix agreement, and actual default construction on the
necessary-and-sufficient side, without assuming a successful update. Final
representation additionally requires the installed default's exact extent and
self-overlay; pending emptiness remains an independent observer law. The no-op
must already have valid backing storing the contents. Output backing validity
is part of these criteria; stored-list equality alone is a weaker observation.

Existing success, total, and cache contracts still validate. Necessity/minimality
of the remaining start, binary range, clone, and geometry laws is not established;
borrowed CoW and model fidelity also remain incomplete. No Rust, extraction,
external model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous apply-updates layer-condition checkpoint (`10447d8`, necessary
selection `16b9b2c`, binary nonzero output `0f38573`, public sufficiency
`2226423`, density `6fb973a`, derived extents `42d7ca1`, input routing
`1474367`): focused and full library builds pass (2,100 jobs). The axiom/import
audit covers 5,708 declarations across all 384 modules: 5,589 use only standard
Lean axioms or none, and 119 additionally use the existing Arc pointer contract.
All 18 new named lemmas use standard Lean axioms or none; private/generated
declarations are included in the inventory. External axiom use is unchanged.
No new axiom or admission was introduced, and `size_of` remains unused.

Skipped-layer agreement and input invariants now derive false-answer occupied
lengths. Positive layer selection is necessary for a dense successful output:
actual binary rebuilding never returns `Zero`, with no metadata, alignment,
map, or clone laws needed for that structural fact. Valid stored materialization
has an exact criterion on both branches, with positive selection and agreement
in skipped layers/suffixes on the rebuilding branch and already-materialized
input backing on the no-op. No progressive range law or agreement is assumed
upfront by these equivalences. Selected binary reflection, retained clone
preservation, packing, and input backing invariants remain in the contracts;
input representation is required only for rebuilding. Installed defaults are
unconstrained. The criterion includes output backing validity, which the
sufficiency proof establishes; equality of stored lists alone is a weaker
observation. The previous contracts remain available and validate, including
the success/total and cache contracts. Termination and remaining binary/clone/
geometry minimality, borrowed CoW, and model fidelity remain incomplete.
No Rust, extraction, external model, or Aeneas source changed; the seven source
suites and 42-root/151-declaration dependency gate were not repeated for this
proof-only work. Debug and Serde remain excluded; TreeHash is deferred outside
the goal.

Previous apply-updates skipped-layer agreement checkpoint (`5a9398e`, read
criterion `5481b38`, necessary agreement `84224a8`, capacity geometry `f146b17`,
contents `b53be68`/`bacc216`, bounds/scope `f3248ed`/`2f3e7bc`): focused and full
library builds pass (2,097 jobs). The axiom/import audit covers 5,667 declarations
across all 381 modules: 5,548 use only standard Lean axioms or none, and 119
additionally use the existing Arc pointer contract. All 22 new named lemmas
use only standard Lean axioms; private/generated declarations are included in
the inventory. External axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused.

False progressive range answers now permit matching pending entries in their
unchanged backing. Complete read preservation through those layers is proved
from actual successful traversal, without packing, shape, clone, or range
correctness assumptions. Under the remaining selected clone and binary range
laws, agreement in skipped layers and suffixes is equivalent to correct backing
reads. With numeric layer extents and selected binary reflection, it is also
equivalent to exact stored materialization. The old stronger contracts are
adapters. These criteria concern actual success and do not constrain installed
default maps; final representation may separately allow default-overlay
compensation. Existing success/total and cache contracts validate but retain
stronger range laws. Necessity of numeric layer extents, binary range/clone/
geometry minimality, borrowed CoW, and model fidelity remain incomplete.
No Rust, extraction, external model, or Aeneas source changed; the seven source
suites and 42-root/151-declaration dependency gate were not repeated for this
proof-only work. Debug and Serde remain excluded; TreeHash is deferred outside
the goal.

Previous apply-updates layer-range checkpoint (`3780516`, density `2416785`,
empty-layer bounds `01415b8`, scope `78cacde`): focused and full library builds
pass (2,093 jobs). The axiom/import audit covers 5,630 declarations across
all 377 modules: 5,511 use only standard Lean axioms or none, and 119 additionally
use the existing Arc pointer contract. All 21 new named lemmas use only
standard Lean axioms; private/generated helpers are included in the inventory.
External axiom use is unchanged. No new axiom or admission was introduced,
and `size_of` remains unused. Progressive density now needs only numeric
occupied-length conditions on layer answers, with reflection confined to
selected binary subtrees. Four public backing/capacity/actual-value overlay
contracts use these weaker laws; existing reflection contracts are adapters.
Content/materialization and termination contracts still use stronger range
laws and validate, along with the cache contracts. Necessity of the numeric
layer conditions, binary range/clone/geometry minimality, borrowed CoW, and
model fidelity remain incomplete. No Rust, extraction, external model, or
Aeneas source changed; the seven source suites and 42-root/151-declaration
dependency gate were not repeated for this proof-only work. Debug and Serde
remain excluded; TreeHash is deferred outside the goal.

Previous apply-updates materialization checkpoint (`dda608d`, equivalence
`034d26b`, suffix reads `19dee5c`): focused and full library builds pass
(2,091 jobs). The axiom/import audit covers 5,600 declarations across all
375 modules: 5,481 use only standard Lean axioms or none, and 119 additionally
use the existing Arc pointer contract. All 10 new named lemmas use only
standard Lean axioms; private/generated helpers are included in the inventory.
External axiom use is unchanged. No new axiom or admission was introduced,
and `size_of` remains unused. Correct materialized backing reads and exact
stored contents are each equivalent to skipped-value agreement under the
selected clone/range and backing laws. Successful materialization now has an
exact capacity/agreement/default-construction criterion with no supplied
skipped-value premise; the combined representation criterion additionally
requires actual default overlay and extent. The no-op materializes exactly
when its backing already stores the merged sequence. Existing sequence,
total, and cache contracts validate. Necessity is proved for materialization;
the separate representation criterion allows compensation by the installed
map. Remaining clone/range/geometry minimality, borrowed CoW extraction, and
model fidelity are incomplete. No Rust, extraction, external model, or Aeneas
source changed; the seven source suites and 42-root/151-declaration dependency
gate were not repeated for this proof-only work. Debug and Serde remain
excluded; TreeHash is deferred outside the goal.

Previous apply-updates skipped-suffix checkpoint (`10c8634`, list contents
`592280c`, bulk contents `ad51425`, scope `25f577f`): focused and full library
builds pass (2,088 jobs). The axiom/import audit covers 5,583 declarations
across all 372 modules: 5,464 use only standard Lean axioms or none, and 119
additionally use the existing Arc pointer contract. All 15 new named lemmas
use only standard Lean axioms; the declaration count includes generated
helpers. External axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused. Generalized content, materialization,
total, and success/representation contracts now need agreement only for
pending values in selected skipped suffixes, instead of the global semantic
maximum bound. The actual checked length supplies the numeric extent bound.
Existing maximum-bound and empty-map contracts remain adapters, and cache
contracts validate. Remaining premise minimality, borrowed CoW extraction,
and model fidelity are incomplete. No Rust, extraction, external model, or
Aeneas source changed; the seven source suites and 42-root/151-declaration
dependency gate were not repeated for this proof-only work. Debug and Serde
remain excluded; TreeHash is deferred outside the goal.

Previous apply-updates maximum-premise checkpoint (`aa023cf`, lower proofs
`f0daba3`): focused and full library builds pass (2,087 jobs). The axiom/import
audit covers 5,566 declarations across all 371 modules: 5,447 use only standard
Lean axioms or none, and 119 additionally use the existing Arc pointer contract.
The three new named lower lemmas and five strengthened public lemmas use only
standard Lean axioms; the declaration count includes generated helpers.
External axiom use is unchanged. No new axiom or admission was introduced,
and `size_of` remains unused. Density needs only a numeric extension bound,
which the actual checked length calculation supplies for `apply_updates`.
Backing validity, occupied-capacity criteria, and representation from the
actual rebuilt values therefore no longer require `MaximumBoundsValues`.
The semantic maximum law remains in content-preservation, materialization,
and total sequence contracts to justify skipping pending values. Existing
total and cache contracts validate. Remaining premise minimality, borrowed
CoW extraction, and model fidelity are incomplete. No Rust, extraction,
external model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous apply-updates overlay checkpoint (`8e80e9c`, success criteria
`5823c1f`, total contracts `40ac435`, materialization `decf6f7`, and foundation
`c338515`): focused and full library builds pass (2,087 jobs). The axiom/import
audit covers 5,558 declarations across all 371 modules: 5,439 use only standard
Lean axioms or none, and 119 additionally use the existing Arc pointer contract.
All nine new named lemmas use only standard Lean axioms; the declaration count
also includes generated helpers. External axiom use is unchanged. No new axiom
or admission was introduced, and `size_of` remains unused. Representation now
has exact actual-rebuild overlay/extent criteria without separate clone identity.
Under selected clone and range/maximum laws, total contracts and exact success
criteria use default maps that preserve the represented contents, allowing
redundant matching entries and maxima below backing length. Pending emptiness
supplies only its observer. The no-op bypasses every rebuilding law; complete
length-result equality has its own criterion without representation or geometry.
Existing empty-map, backing, and cache contracts validate. Remaining premise
minimality, borrowed CoW extraction, and model fidelity are incomplete. No Rust,
extraction, external model, or Aeneas source changed; the seven source suites and
42-root/151-declaration dependency gate were not repeated for this proof-only
work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.

Previous Arbitrary overlay checkpoint (`16befa3`, success criteria `f93004f`,
foundation `b8f058f`): focused and full library builds pass (2,084 jobs).
The axiom/import audit covers 5,547 declarations across all 368 modules:
5,428 use only standard Lean axioms or none, and 119 additionally use the
existing Arc pointer contract. All nine new lemmas use only standard Lean
axioms; external axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused. Both generator entry points now
have exact success and representation criteria with actual control/element
traces and the same consumed-input state. The owning default recovers the
state it discards. Total generation and successful-state contracts use exact
map overlay/extent laws, with emptiness supplying only the pending observer;
existing empty-map and cache contracts validate through these results.
Remaining premise minimality, borrowed CoW extraction, and model fidelity are
incomplete. No Rust, extraction, external model, or Aeneas source changed;
the seven source suites and 42-root/151-declaration dependency gate were not
repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
is deferred outside the current goal.

Previous decoder overlay checkpoint (`decd3f9`, trace criteria `5c49998`,
foundation `5b8202a`): focused and full library builds pass (2,082 jobs).
The axiom/import audit covers 5,538 declarations across all 366 modules:
5,419 use only standard Lean axioms or none, and 119 additionally use the
existing Arc pointer contract. All nine named new lemmas and the two generated
helpers for `represents_nil_iff` use only standard Lean axioms; external axiom
use is unchanged. No new axiom or admission was introduced, and `size_of`
remains unused. Public decoding now has exact default-map representation and
success criteria tied to actual consumed payloads. General trace and both
canonical-format total contracts derive execution and representation/backing
results under those laws; pending emptiness supplies only its observer.
Empty-input packing and metadata bypasses are preserved. Existing empty-map
contracts and dependent roundtrip, cache, and other proofs build. Arbitrary's
default-map audit, remaining premise minimality, borrowed CoW extraction, and
model fidelity are incomplete. No Rust, extraction, external model, or Aeneas
source changed; the seven source suites and 42-root/151-declaration dependency
gate were not repeated for this proof-only work. Debug and Serde remain
excluded; TreeHash is deferred outside the current goal.

Previous constructor overlay checkpoint (`a756c07`, total contracts `a32454f`,
foundation `75701ea`): focused and full library builds pass (2,080 jobs).
The axiom/import audit covers 5,527 declarations across all 364 modules:
5,408 use only standard Lean axioms or none, and 119 additionally use the
existing Arc pointer contract. All twelve new lemmas use only standard Lean
axioms; external axiom use is unchanged. No new axiom or admission was
introduced, and `size_of` remains unused. All four sequence constructors now
have exact default-map representation and success-and-representation
criteria, with actual iterator consumption inferred from successful calls.
Their generalized total contracts derive execution and representation/backing/
spine results; pending emptiness is a separate observer law. Existing
empty-map contracts and all dependent decoder, cache, and other proofs build.
Packing layout and geometry retain their stated roles; remaining premise
minimality, borrowed CoW extraction, and model fidelity are incomplete.
No Rust, extraction, external model, or Aeneas source changed; the seven source
suites and 42-root/151-declaration dependency gate were not repeated for this
proof-only work. Debug and Serde remain excluded; TreeHash is deferred outside
the current goal.

Previous front-removal overlay checkpoint (`45f8783`, foundations `7801d06`
and `9dd67d2`): focused and full library builds pass (2,078 jobs). The
axiom/import audit covers 5,515 declarations across all 362 modules: 5,396 use
only standard Lean axioms or none, and 119 additionally use the existing Arc
pointer contract. All five new lemmas use only standard Lean axioms; external
axiom use is unchanged. No new axiom or admission was introduced, and
`size_of` remains unused. Front-removal representation and successful
preserving execution now have exact clone/default-map overlay and extent
criteria, including the zero branch. Existing dense-backing representation
and front-removal content/total contracts use the general results. The full
build also validates all constructor, decoder, and other dependent proofs.
Input representation and geometry retain their stated roles; remaining
premise minimality, borrowed CoW extraction, and model fidelity are incomplete.
No Rust, extraction, external model, or Aeneas source changed; the seven source
suites and 42-root/151-declaration dependency gate were not repeated for this
proof-only work. Debug and Serde remain excluded; TreeHash is deferred outside
the current goal.

Previous representation-criteria checkpoint (`594f218`, foundations `eef66e2`
and `297cfd4`): focused and full library builds pass (2,075 jobs). The
axiom/import audit covers 5,510 declarations across all 359 modules: 5,391 use
only standard Lean axioms or none, and 119 additionally use the existing Arc
pointer contract. Ten new declarations reuse that contract. No new axiom or
admission was introduced, and `size_of` remains unused. The new criteria prove
necessity and sufficiency of actual map-clone read/extent outcomes for
nonmutating sequence preservation, and combine them with backing readiness
for exact successful-preserving-execution criteria. Total contracts derive
all calls and representation/backing/metadata results; existing downstream
cache and validity contracts validate through the new adapters. Full-result
lookup equivalences also cover failure/divergence without representation or
map-read-success premises. Layout/backing geometry and selected content
soundness remain explicit where needed for traversal and semantic correctness;
minimality of every premise, borrowed CoW, and model fidelity are incomplete.
No Rust, extraction, external model, or Aeneas source changed. The seven source
suites and 42-root/151-declaration model dependency gate were not repeated for
this proof-only work. Debug and Serde remain excluded, and TreeHash remains
deferred outside the goal.

Previous selected-cache checkpoint (`e88ce19`, foundations `2307f24`,
`c20e293`, `c31c8bb`, `9db36ad`, and `f9da88a`): focused and full library
builds pass (2,072 jobs). The axiom/import audit covers 5,497 declarations
across all 356 modules: 5,388 use only standard Lean axioms or none, and 109
additionally use the existing Arc pointer contract. Five new cache-equivalence
declarations use that contract, while the existing action classifier no
longer does, for a net increase of four. Both general and dense-input
classifier proofs use only standard Lean axioms. No new axiom or admission
was introduced, and `size_of` remains unused. Under selected content soundness
and actual success, selected cache inputs are necessary and sufficient for
both public results' cache validity without global layout, geometry, density,
capacity, accurate-length, query-success, map, or representation premises.
Existing cache contracts use the general result through dense-input adapters.
Semantic-premise minimality, borrowed CoW extraction, and model fidelity remain
incomplete. No Rust, extraction, external model, or Aeneas source changed;
the 42-root/151-declaration dependency gate and seven source suites were not
repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
remains deferred outside the current goal.

Previous selected-content checkpoint (`c8724e7`, foundations `78d9600`,
`b166ec0`, `aa0bb68`, `5832bf5`, `47c372e`, and `1fa4dbc`): focused and full
library builds pass (2,065 jobs). The axiom/import audit covers 5,450
declarations across all 349 modules: 5,345 use only standard Lean axioms or
none, and 105 additionally use the existing Arc pointer contract. Eight
additional declarations reuse that contract; no new axiom or admission was
introduced, and `size_of` remains unused. Exact materialized rebase contents
now require only selected semantic soundness and actual success, with no
layout, shape, density, capacity, accurate-length, comparison-termination, or
query-success premise. The progressive obligations follow actual queries and
clamped metadata. Merged-sequence contracts retain geometry/layout for indexed
traversal and the nonmutating clone's fallback-aware reads and logical extent.
Existing binary/progressive/public content contracts are adapters to the
general results. The remaining assumption audit, borrowed CoW, and model
fidelity are incomplete. No Rust, extraction, external model, or Aeneas source
changed; the 42-root/151-declaration model dependency gate and seven source
suites were not repeated for this proof-only work. Debug and Serde remain
excluded; TreeHash remains deferred and outside the current goal.

Previous packing-query checkpoint (`3231f6f`, foundations `d1ba797`, `4952ade`,
`cb7e79e`): focused and full library builds pass (2,060 jobs). The axiom/import
audit covers 5,430 declarations across all 344 modules: 5,333 use only standard
Lean axioms or none, and 97 additionally use the existing Arc pointer contract.
Seven additional declarations reuse that contract. No new axiom or admission
was introduced; `size_of` remains unused. The complete public success criteria
have no separate packing-layout, global query-success, shape, capacity,
density, accurate-length, or semantic comparison/hash premise. Packing queries
are required only for entered node pairs and are recovered from actual
successful execution; their exact helper outcomes, including the logarithm
result for packed factors, remain explicit conditions rather than a blanket
metadata-totality assertion. Nonmutating rebase still requires its actual map
clone to return on every branch. Existing progressive/public success lemmas
and total contracts now use this criterion through invariant adapters.
Packing and geometry for content/cache correctness, remaining assumption
review, borrowed CoW, and model fidelity remain open. No Rust, extraction,
external model, or Aeneas source changed; the 42-root/151-declaration model
dependency gate and source suites were not repeated for this proof-only work.
Debug, Serde, and TreeHash remain outside the current scope.

Previous selected-geometry checkpoint (`2d63438`, foundations `15af31a`,
`9e1c78c`, `9afa364`, `dfe9e73`): focused and full library builds pass (2,057
jobs). The axiom/import audit covers 5,399 declarations across all 341 modules:
5,309 use only standard Lean axioms or none, and 90 additionally use the
existing Arc pointer contract. Nine additional declarations reuse that
contract; no new axiom or admission was introduced, and `size_of` remains
unused. Both public success criteria now omit whole-tree shape and
representable-layer assumptions. At a fixed packing layout they characterize
success by only reached depth/shape/shift checks and element calls, plus the
actual pending-map clone for nonmutating rebase. Both machine clamps are
retained in progressive layer lengths. Existing progressive and public
success lemmas, and the total contents/cache contracts that use them, now
build on the general result through invariant adapters. Geometry for content
and cache correctness, packing assumptions, remaining assumption review,
borrowed CoW, and model fidelity remain open. No Rust, extraction, external
model, or Aeneas source changed; the 42-root/151-declaration model dependency
gate and source suites were not repeated for this proof-only work. Debug,
Serde, and TreeHash remain outside the current scope.

Previous rebase success-conditions checkpoint (`d5836d4`, foundations `3f2f4fa`,
`c3ff39d`, `212ac40`): focused and full library builds pass (2,052 jobs). The
axiom/import audit covers 5,314 declarations across all 336 modules: 5,233 use
only standard Lean axioms or none, and 81 additionally use the existing Arc
pointer contract. Of the 34 new declarations, 24 use only standard axioms or
none, and ten reuse that pointer contract. No new axiom or admission was
introduced; `size_of` remains unused. Both public success equivalences require
precisely the selected element comparisons to terminate, plus the actual
pending-map clone for nonmutating rebase, under packing layout, compatible
shapes, and representable original layers. Reflection recovers those
comparisons from actual successful calls; binary reflection needs no geometry,
and progressive reflection needs only layout and original capacity. No
density, accurate input-length metadata, semantic equality/hash law, or
map-preservation law is needed for these termination criteria. The geometry
conditions and semantic correctness have separate audit obligations. No Rust,
extraction, external model, or Aeneas source changed; the 42-root/151-declaration
model dependency gate and source suites were not repeated for this proof-only
work. Remaining assumption review, borrowed CoW, and model-fidelity work stay
open. Debug, Serde, and TreeHash remain outside the current scope.

Previous rebase cache-equivalence checkpoint (`ad4e3f4`, foundations `0dc26d2`,
`01b05f5`): focused and full library builds pass (2,048 jobs). The axiom/import
audit covers 5,280 declarations across all 332 modules: 5,209 use only standard
Lean axioms or none, and 71 additionally use the existing Arc pointer contract.
The seven new binary/progressive/public operation lemmas account for the
additional pointer-contract dependencies. No new axiom or admission was
introduced; `size_of` remains unused. Both public cache equivalences recover
actual clone/rebase calls and prove the retained-original/imported-base laws
jointly necessary and sufficient, under the existing content laws and input
geometry. They assume no cache validity, represented sequence, or pending-map
law. No Rust, extraction, external model, or Aeneas source changed; the
42-root/151-declaration model dependency gate and source suites were not
repeated for this proof-only work. Remaining assumption review, borrowed CoW,
and model-fidelity work stay open. Debug, Serde, and TreeHash remain outside
the current scope.

Previous original-cache checkpoint (`01f0d4f`, foundations `a653121`, `8173c77`):
focused and full library builds pass (2,045 jobs). The axiom/import audit covers
5,257 declarations across all 329 modules: 5,193 use only standard Lean axioms
or none, and 64 additionally use the existing Arc pointer contract. The new
pointer-equality helper accounts for the one additional dependency; all 21
new scope declarations use only standard axioms or none. No new axiom or
admission was introduced, and `size_of` remains unused. Eight successful/total
public cache contracts require validity only for retained original caches,
with reached original hash-shortcut validity supplied separately to the
reference collision bridges. The error-inclusive wrapper keeps full original
validity; cleared-input results derive both selected laws. All eleven public
cache/validity contracts build. No Rust, extraction, external model, or Aeneas
source changed; the 42-root/151-declaration model dependency gate and source
suites were not repeated for these proof-only changes. Remaining assumption
review, borrowed CoW, and model-fidelity work stay open. Debug, Serde, and
TreeHash remain outside the current scope.

Previous binary base-cache checkpoint (`99fad96`, foundation `b7e16e2`): focused
and full library builds pass (2,041 jobs). The axiom/import audit covers 5,235
declarations across all 325 modules: 5,172 use only standard Lean axioms or
none, and 63 additionally use the existing Arc pointer contract. The new
action-category reflection accounts for the one additional pointer-contract
dependency; no new axiom or admission was introduced, and `size_of` remains
unused. Binary/progressive preservation, both finite-collision bridges, and
all eleven public cache/validity contracts validate with base validity scoped
to the input-based action categories. No Rust, extraction, external model,
or Aeneas source changed; the 42-root/151-declaration model dependency gate
and source suites were not repeated for these proof-only changes. The
classifier is a checked proof artifact and does not replace an extracted
body. Original-cache assumptions, borrowed CoW, and remaining model-fidelity
work stay open. Debug, Serde, and TreeHash remain outside the current scope.

Previous selected base-cache checkpoint (`1547078`, foundation `e512df3`):
focused and full library builds pass (2,038 jobs). The axiom/import audit covers
5,141 declarations across all 322 modules: 5,079 use only standard Lean axioms
or none, and the same 62 additionally use the Arc pointer contract. The new
scope and adapters introduce no axioms or admissions; `size_of` remains unused.
All eleven public rebase cache/validity contracts now omit base-cache premises
for absent and pointer-shared progressive suffixes. The finite-collision
bridge uses the same selected base layers. Cache validity inside each reached
binary layer remains a separate assumption-review item. No Rust, extraction,
external model, or Aeneas source changed; the 42-root/151-declaration model
dependency gate and source-model suites were not repeated for this proof-only
change. Borrowed CoW and remaining assumption/model-fidelity work stay open.
Debug, Serde, and TreeHash remain outside the current scope.

Previous packed rebase soundness checkpoint (`fbf2a27`, with foundation
`e9ada7a`): focused and full library builds pass (2,037 jobs). The axiom/import
audit covers 5,127 declarations across all 321 modules: 5,065 use only standard
Lean axioms or none, and 62 additionally use the existing Arc pointer contract.
All new packed-comparison criteria and the rebase branch equivalence use only
standard Lean axioms or none; `size_of` remains unused. No new axiom or
admission was introduced. Packed soundness now requires element agreement only
when all paired `ne` calls return false, a condition proved equivalent to
soundness of the positive vector result. All dependent public rebase contents
and cache proofs validate with this weaker law. No Rust, extraction, external
model, or Aeneas source changed; the dependency inventory remains 42 roots/151
local declarations, and source-model suites were not repeated for this
proof-only change. Borrowed CoW and remaining assumption/model-fidelity work
stay open; Debug, Serde, and TreeHash remain outside the current scope.

Previous write-back lookup checkpoint (`7d329d7`, with foundations `a027551`
and `ac16012`): focused and full library builds pass (2,036 jobs). The
axiom/import audit covers 5,117 declarations across all 320 modules: 5,055 use
only standard Lean axioms or none, and 62 additionally use the existing Arc
pointer contract. All five new foundation criteria/adapters and all eleven
new or revised public write-back results use only standard Lean axioms. The
`size_of` axiom remains unused; no new axiom or admission was introduced.
Mutable and consuming CoW sequence contracts now require agreement of raw
lookup outcomes after the original backing fallback. Joint lookup/maximum
equivalences prove these conditions necessary and sufficient for the
represented replacement, including the selected value supplied by the backing
tree. Initial read/clone contracts, actual CoW entry/metadata footprints, and
the existing theorem conclusions are retained. No Rust, extraction, external
model, or Aeneas source changed. The model dependency inventory remains
42 roots/151 local declarations; that gate was not repeated for these
proof-only changes. Borrowed CoW and the remaining assumption/model-fidelity
review stay open.

Previous append lookup checkpoint (`2e4927d`, with lookup foundations `79bd2a6`):
focused and full library builds pass (2,035 jobs). The axiom/import audit covers
5,108 declarations across all 319 modules: 5,046 use only standard Lean axioms
or none, and 62 additionally use the existing Arc pointer contract. All three
new foundation lemmas and all six new or revised public append results use
only standard Lean axioms. The `size_of` axiom remains unused; no new axiom or
admission was introduced. Indexed read-back, sequence, and total append
contracts now require exact pending lookup only at the appended key; other
queries need agreement after the original backing fallback. The new sequence
equivalence proves these lookup and maximum conditions jointly necessary and
sufficient, and the total proof uses it. The existing theorem conclusions are
unchanged. No Rust, extraction, external model, or Aeneas source changed. The
model dependency inventory remains 42 roots/151 local declarations; that gate
was not repeated for these proof-only changes. Borrowed CoW and the remaining
assumption/model-fidelity review stay open.

Previous clone lookup checkpoint (`b93748b`, with raw/public lookup criteria
`38c8b6d`): focused and full library builds pass (2,034 jobs). The axiom/import
audit covers 5,099 declarations across all 318 modules: 5,037 use only standard
Lean axioms or none, and 62 additionally use the existing Arc pointer contract.
All 18 declarations in the two new lookup modules, and all clone criteria,
use only standard Lean axioms. The `size_of` axiom remains unused; no new axiom
or admission was introduced. Clone, clone_from, and dependent rebase
sequence/cache contracts now permit different raw map reads when they agree
after the actual backing fallback. Joint lookup/extent equivalences prove
these conditions necessary and sufficient for sequence-preserving clones.
The same theorem conclusions and separate pending-observer laws are retained.
No Rust, extraction, external model, or Aeneas source changed. The model
dependency inventory remains 42 roots/151 local declarations; that separate
gate was not repeated for these proof-only changes. Borrowed CoW and the
remaining assumption/model-fidelity review stay open.

Previous append-maximum checkpoint (`693bd6d`, with general length criteria
`d7af67d`): focused builds and the full library build pass (2,032 jobs).
The axiom/import audit covers 5,081 declarations across all 316 modules:
5,019 use only standard Lean axioms or none, and 62 additionally use the
existing Arc pointer contract. Both general length criteria, both public
append equivalences, and the revised length and total append proofs use only
standard Lean axioms. The `size_of` axiom remains unused; no new axiom or
admission was introduced. The exact maximum premise for successful append
is necessary because the new extent strictly exceeds the unchanged backing
length. Its sequence equivalence is conditional on the reached insertion's
lookup law and does not establish minimality of other map assumptions or
concrete implementation fidelity. No Rust, extraction, external model, or
Aeneas source changed. The model dependency inventory remains 42 roots/151
local declarations; that gate was not repeated for these proof-only changes.
Borrowed CoW and the remaining assumption/model-fidelity review stay open.

Previous write-back metadata checkpoint (`70a420e`, with generic laws
`242e0f1`): focused builds and the full library build pass (2,031 jobs).
The axiom/import audit covers 5,073 declarations across all 315 modules:
5,011 use only standard Lean axioms or none, and 62 additionally use the
existing Arc pointer contract. All three new generic implications and all
nine new or revised public write-back results use only standard Lean axioms.
The `size_of` axiom remains unused; no new axiom or admission was introduced.
Mutable and consuming CoW sequence contracts require maximum-result agreement
at the original backing length instead of exact insertion metadata. Both
public length equivalences prove that relation necessary and sufficient for
complete result preservation, and both successful-length corollaries drop
their separate index bounds. The retained exact insertion laws imply the new
contracts for writes below an existing successful logical end. No Rust,
extraction, external model, or Aeneas source changed. The model dependency
inventory remains 42 roots/151 local declarations; that separate gate was not
repeated for these proof-only changes. Borrowed CoW and the remaining
assumption/model-fidelity review stay open.

Previous rebase-observer checkpoint (`dab2f4e`, with criterion `dd3f4c6`): the
focused build and full library build pass (2,031 jobs). The axiom/import audit
covers 5,070 declarations across all 315 modules: 5,008 use only standard Lean
axioms or none, and 62 additionally use the existing Arc pointer contract.
All 53 declarations in `UpdateMap.Length.Equivalence`, including generated
lemmas, and both new public equivalences use only standard Lean axioms.
The `size_of` axiom remains unused. No new axiom or admission was introduced.
The nonmutating rebase observer theorem now requires exactly the relevant
maximum/emptiness behavior of the actual map clone, rather than maximum
identity. No Rust, extraction, external model, or Aeneas source changed.
The model dependency inventory remains 42 roots/151 local declarations; that
separate gate was not repeated for these proof-only changes. Borrowed CoW and
the remaining assumption/model-fidelity review stay open.

Previous source-model checkpoint (`4cbc263`): actual SSZ encoder construction
now compares with the local model for every buffer and fixed-byte count,
including its buffer-release continuation on every replacement encoder state.
The proof retains the existing concrete `Vec::reserve` model explicitly and
requires no caller-supplied bound or success premise. It uses only `propext`.
This establishes construction relative to that primitive; Rust reservation,
allocation, and capacity behavior are not independently verified.
The runner validates the missing primitive's `alloc` source provenance and
exact template declaration/signature. The generated axiom template is never
compiled. An import-only module supplies the existing concrete definition;
generated source bodies remain untouched. The report records this retained
local foundation, and other suites retain their strict template rejection.
Seven malformed templates, seven invalid foundation inventories, four invalid
binding configurations, and four invalid axiom reports are rejected.
Eight SSZ native tests pass, including constructor release, reservation
overflow, payload movement/clearing, repeated finalization, and callback-panic
write order. Direct append and finalization still fail on stored mutable-buffer
borrows (UPSTREAM_BUGS 26); their native checks are not source proofs.
All seven source suites pass: 33 direct comparisons and two compositions,
for 35 proofs (16 axiom-free, nineteen standard-only). No production Rust,
local model, main proof, or Aeneas source changed. The main gate was not
repeated for this standalone audit; its latest pass remains 5,117 declarations
across 320 modules and 2,036 build jobs. The model inventory remains 42
roots/151 declarations. Borrowed CoW and the remaining model/assumption review
stay open. Debug and Serde remain excluded; TreeHash remains deferred.

Earlier source-model checkpoint (`e396dad`): both Arbitrary size-hint defaults
now compare directly with their actual source bodies for arbitrary dictionaries
and depths. The complete dictionary adapter retains every callback. The fixed
default ignores them all; the fallible default preserves the actual hint's
success, failure, and divergence. Both equalities hold by reflexivity without
callback-consistency, termination, or depth premises. The fixed comparison
uses only the three standard Lean axioms; the fallible comparison uses only
`propext`.
The audit excludes exactly the unused owning-input default and verifies that
all three compared source declarations remain equal after reconciling Charon's
fresh statement IDs. The runner checks unique integer-ID correspondence and
records all nineteen changes; source spans, code, signatures, and callable IDs
remain unchanged. A name-only change to the generic trait's first field avoids
namespace shadowing. Restoring the field's two labels and the source error
type name must recover the entire original selected LLBC.
Nine malformed source inventories, fifteen invalid trait/metadata/configuration
cases, nine invalid exclusion/statement cases, and four invalid axiom reports
are rejected. Eight native tests pass, including exact hint-callback panic
dispatch. All seven source suites pass: 32 direct comparisons and two
compositions, for 34 proofs (16 axiom-free, eighteen standard-only).
No production Rust, local model, main proof, or Aeneas source changed. The
main gate was not repeated for this standalone audit; its latest pass remains
5,117 declarations across 320 modules and 2,036 build jobs. The model inventory
remains 42 roots/151 declarations. Arbitrary's owning default/vector generator,
borrowed CoW, and the remaining model/assumption review stay open. Debug and
Serde remain excluded; TreeHash remains deferred.

Earlier source-model checkpoint (`db45ecc`): the Arbitrary suite compares the
actual Boolean generator with `nextControl` for every input slice. The proof
follows the actual byte generator, one-byte prefix copy, zeroing loop and
write-back, and low-bit test. Both the result and remaining input agree,
including consumption of even stopping bytes and zero at exhaustion. No
input-length, success, or termination premise is added; the proof uses only
standard Lean axioms. The one-byte helper covers the buffer width reached by
this path, not arbitrary buffer widths.
The runner distinguishes the bool method's module from the identically named
byte method and checks type provenance independently. Renaming only the source
error type avoids a generated instance collision; restoring its metadata
must recover the entire original LLBC. Ten malformed source inventories, ten
invalid metadata/type-namespace cases, and four invalid axiom reports are
rejected. Seven native tests cover all control bytes, buffer overwrite,
first-error/panic input state, custom input replacement, and default dispatch.
Full vector generation and all three trait defaults remain source boundaries;
the verified owning-default/vector extraction failures are UPSTREAM_BUGS 27.
All seven source suites pass: 30 direct comparisons and two compositions,
for 32 proofs (16 axiom-free, sixteen standard-only). No production Rust, local
model, main proof, or Aeneas source changed. The main gate was not repeated
for this standalone audit; its latest pass remains 5,117 declarations across
320 modules and 2,036 build jobs. The model inventory remains 42 roots/151
declarations. Borrowed CoW and the remaining model/assumption review stay open.
Debug and Serde remain excluded; TreeHash remains deferred.

Earlier source-model checkpoint (`c0d7c7f`): the SSZ offset suite compares the
actual constant and private decoder with the local model, and separately proves
the public reader's prefix-slicing composition. The complete four-copy loop,
checked increments, termination, and all length/error cases are proved without
additional premises. All three comparisons use only standard Lean axioms.
The shared runner validates original source provenance, then verifies that
retaining the private root and renaming the source error enum are the only
LLBC changes. Nine malformed source inventories, eighteen invalid metadata,
provenance, or configuration cases, and four invalid axiom reports are rejected.
Four native tests cover exact short-input errors, all 32 bits and extrema,
mixed-byte order and ignored suffixes, and debug-profile oversized-offset
rejection. Direct public-reader extraction still fails on a borrowed temporary;
direct encoding emits a missing `Usize.to_le_bytes` identifier (UPSTREAM_BUGS 26).
All six source suites pass: 29 direct comparisons and two separate compositions,
for 31 proofs (16 axiom-free, fifteen standard-only). No production Rust, local
model, main library proof, or Aeneas source changed. The main gate was not
repeated for these standalone checks; its latest pass remains 5,117
declarations across 320 modules and 2,036 build jobs. The model inventory
remains 42 roots/151 declarations. Borrowed CoW and the remaining model and
assumption review stay open. Debug and Serde remain excluded; TreeHash remains
deferred.

Earlier source-model checkpoint (`1a575ec`): the vector suite adds three
comparisons against pinned `is_empty`, `eq`, and `ne` bodies. All hold without
extra callback, termination, or word-bound premises, retaining the existing
vector/index/slice foundation models. Their standard-only proofs preserve
actual `ne` dispatch and all callback results. The shared runner exposes
comparison bodies hidden by builtin matching through two name-only metadata
changes and verifies that the complete remaining LLBC is identical.
Nine malformed source inventories, ten invalid renames or extra mutations,
and four malformed or excessive axiom reports are rejected. Six native tests
pass, including removal/iteration movement, capacity, zero-sized elements,
exhaustion, and drop behavior. Direct `pop`/`next_back` extraction is still
unresolved at container field/type analysis (UPSTREAM_BUGS 25).
All five source suites pass: 27 direct comparisons and the separate Option
cloned composition, for 28 proofs (16 axiom-free, twelve standard-only).
No production Rust, local model, main library proof, or Aeneas source changed.
The main gate was not repeated for these standalone checks; its latest pass
remains 5,117 declarations across 320 modules and 2,036 build jobs. The model
inventory remains 42 roots/151 declarations. Borrowed CoW and remaining
numeric/container/model/assumption review stay open. Debug and Serde remain
excluded; TreeHash remains deferred.

Earlier source-model checkpoint (`c948ef8`): the tuple suite adds four direct
comparisons for arbitrary callback results, with four native tests covering
59 short-circuit, dispatch, and panic combinations. Equality and inequality
are axiom-free; partial and total ordering use only `propext`, already present
in the local ordering model definitions. No callback-consistency or termination
premise is added. The shared runner verifies dependency module provenance and
requires identical expanded source declarations before and after excluding
four unused ordering defaults. Nine malformed source inventories, a changed
body after exclusions, and four malformed or excessive axiom reports are
rejected. All four source suites pass: 24 direct comparisons and the separate
Option cloned composition, for 25 proofs (16 axiom-free, nine standard-only).
No production Rust, local model, main library proof, or Aeneas source changed.
The main library gate was not repeated for these standalone checks; its latest
passing checkpoint remains 5,117 declarations across 320 modules (2,036 build
jobs). The 42-root/151-declaration dependency inventory is unchanged. Borrowed
CoW, three numeric intrinsic boundaries, and remaining model/assumption review
stay open. Debug and Serde remain excluded; TreeHash remains deferred.

Earlier fixed-byte checkpoint (`c3e0616`): five direct comparisons and four
native tests pass for the pinned dependency's clone, equality, ZERO, default,
and `is_zero`, at every array length and byte input. The runner verifies
constant-initializer links and dependency provenance; eleven malformed
inventories and four malformed axiom reports are rejected. All three source
suites pass: 20 direct comparisons plus the separate Option cloned
composition, for 21 proofs (14 axiom-free, seven standard-only). No production
Rust, local model, main library proof, or Aeneas source changed. The main
library gate was not repeated; its counts remain 5,015 declarations across
314 modules. Borrowed CoW and the remaining model/assumption review are open.

Previous core-model checkpoint (`3182fd0`): the source audit also proves
`u128::checked_pow` equals its actual extracted squaring loop for every base
and exponent. Exponent-halving termination and sound intermediate-overflow
detection are derived internally; the public equality has no arithmetic or
termination premise. All four comparisons and seven native tests pass,
including 77 checked-power reference pairs and eight large-exponent cases.
Only standard Lean axioms and the existing arithmetic foundation are used.
The three missing-intrinsic boundaries and borrowed CoW remain open. No
production/model/library change was made; the main-library audit was not
repeated and its totals remain 5,015 declarations across 314 modules.

Previous core-model checkpoint (`5be93e6`): the source audit additionally proves
`u128::saturating_mul` equals its actual extracted body for all inputs, using
only standard Lean axioms and the existing checked-multiplication foundation.
All three source comparisons and five native tests pass. The checked-power
loop extracts but its equality remains unproved. Three other numeric helpers
retain missing intrinsic templates; broader inclusion also exposes unsupported
overflow-pair operations (UPSTREAM_BUGS issue 24). No production/model/library
change or new axiom was made. These standalone checks leave the previous
main-library totals unchanged at 5,015 theorem declarations across 314 modules;
the full library audit was not repeated for this addition. The goal remains
incomplete, including borrowed CoW and the remaining model/assumption review.

Previous core-model checkpoint (through `06f8825`, with comparisons `5541c30`):
`python3 scripts/aeneas-audit-core-models.py` passes after fresh extraction of
`mem::take` and `usize::div_ceil`. The former comparison is axiom-free; the
latter uses only standard Lean axioms and requires no positivity or size
bound. Rust formatting and all four native protocol/boundary tests pass.
The existing Option audit also passes after moving both suites to a shared
runner, retaining its twelve axiom-free checks and its explicit unresolved
direct `cloned` extraction. Eleven malformed core audit inputs and an injected
axiom in an Option comparison are rejected. These standalone checks change
no production Rust, model body, main library proof, or Aeneas source. Earlier
main-library build/axiom and dependency results remain applicable and were
not repeated. Borrowed CoW and the remaining assumption/model-fidelity review
stay open.

Previous Option-model checkpoint (through `72abe24`, with comparisons `3732fe7`):
`python3 scripts/aeneas-audit-option-models.py` passes after fresh extraction
of eleven explicitly included standard-library bodies. All eleven direct
comparisons and the separate `cloned` composition theorem validate without
axioms. The focused external-model build, Rust formatting, and both native
clone-protocol tests pass; seven malformed inventory/report inputs are
rejected. Direct `cloned` extraction remains unresolved and is recorded
separately, with no partial generated files imported. No production Rust,
external model, library proof, or Aeneas source changed. The main library
build/audit and dependency inventory from earlier checkpoints remain
applicable and were not repeated for these standalone checks. Borrowed CoW
and the remaining assumption/model-fidelity review stay open.

Previous clone-maximum checkpoint (through `6b3cba2`, with criterion `e835ed8`):
the clone, clone_from, and dependent rebase focused builds pass. The full
library build passes (2,030 jobs), and the axiom/import audit covers 5,015
theorem declarations across all 314 modules. Of these, 4,953 use only standard
Lean axioms or none; 62 additionally use the existing Arc pointer contract.
All five declarations attributed to `Clone.Maximum`, including generated
lemmas, are standard-only. The `size_of` axiom remains unused, and no new axiom
or admission was introduced.
The new maximum-index criterion is necessary and sufficient for sequence
preservation under read agreement. Public cloning and the rebasing contracts
that use it no longer require exact maximum identity; they use the returned
maximum's logical extent and derive successor safety from representation.
No Rust, extraction, external model, or Aeneas source changed. The previous
model dependency inventory remains applicable; that separate gate was not
rerun for these proof-only changes. Borrowed CoW and the remaining
assumption/model-fidelity review stay open.

Previous variable-encoder checkpoint (through `a72ca45`, with append laws
`9270e05` and append-call equations `27873f1`): all focused builds pass,
including the variable decoder roundtrip. The full library build passes
(2,029 jobs), and the axiom/import audit covers 5,012 theorem declarations
across all 313 modules. Of these, 4,950 use only standard Lean axioms or none;
62 additionally use the existing Arc pointer contract. All 19 declarations
in the two new call modules, including generated lemmas, are standard-only.
The `size_of` axiom remains unused; no new axiom or admission was introduced.
Variable append laws now apply only to preceding temporary payload buffers.
The call equations retain actual encoder state and continuation composition,
reservation, finalization, and failure/divergence without codec or byte/offset
bounds. The size-call equations retain element calls and checked arithmetic
in order without size laws or byte bounds, including overflow before later
calls. No Rust, extraction, external model, or Aeneas source changed. The
previous model dependency inventory remains applicable; the separate gate
was not rerun for these proof-only changes. Borrowed CoW and the remaining
assumption/model-fidelity review stay open.

Previous fixed-encoder checkpoint (through `f2f8a43`, with call equations
`25504ce` and separate bounds `8856ba2`): the focused builds pass, including
the fixed decoder roundtrip. The full library build passes (2,027 jobs), and
the axiom/import audit covers 4,993 theorem declarations across all 311
modules. Of these, 4,931 use only standard Lean axioms or none; 62 additionally
use the existing Arc pointer contract. All ten declarations in `FixedCalls`,
including generated lemmas, are standard-only; `size_of` remains unused.
The new call equations preserve actual returned buffers, failure, and
divergence without codec laws. Exact fixed-byte specifications no longer
require declared width to match payload length and constrain append behavior
only on buffers reached from preceding payloads. The decoder roundtrip keeps
width coherence for its chunk boundaries.
No Rust, extraction, external model, or Aeneas source changed. The previous
model dependency inventory remains applicable; that separate gate was not
rerun for these proof-only changes. Borrowed CoW and the remaining
assumption/model-fidelity review stay open.

Previous packing-layout checkpoint (through `0932572`, with numeric foundation
`69d2ec6`): the invariant, builder, and repeat focused builds pass after removing
the redundant depth-query premise from both layout constructors. The full
library build passes (2,026 jobs), and the axiom/import audit covers 4,983
theorem declarations across all 310 modules. Of these, 4,921 use only standard
Lean axioms or none; 62 additionally use the existing Arc pointer contract.
All 25 declarations in the two new proof modules, including private and
generated lemmas, are standard-only. The `size_of` axiom remains unused.
The model dependency gate passes for the same 42 roots and 151 local model
declarations.
No Rust, extraction, external model, or Aeneas source changed; no new axiom or
admission was introduced. The factor query and routing power law now derive
the previously assumed depth result for all dependent operation contracts.
Borrowed CoW and the remaining assumption/model-fidelity review stay open.

Previous borrowed-read diagnostic checkpoint (through `56924d0`): a standalone
[reference-layout reproducer](reproducers/cow_regions/README.md) tests lifetime
separation without map dependencies. Eight enum readers, including separate
lifetimes, helper calls, and direct-copy patterns, still fail at Aeneas's
shared-loan lookup. Four plain/nested/struct controls translate successfully;
their separately generated Lean bodies compile and four value lemmas validate
without axioms. Native Rust checks and formatting pass. This rules out the
tested approaches but does not prove a borrowed CoW method or establish that
every refactor is impossible. No production Rust, extraction, imported proof,
model, or Aeneas source changed, and no partial generated file was imported.
At that diagnostic checkpoint, the last complete library build and audits
were the tuple checkpoint below.

Latest tuple-model checkpoint (through `c47faba`): the external tuple `ne`
model now preserves the pinned Rust element-method dispatch and short-circuit
order. Six branch/result lemmas fail against the old model and pass with the
correction. Four native protocol tests and their formatting check pass. The
full library build passes (2,024 jobs); the axiom/import audit covers 4,965
theorem declarations across 308 modules. Of these, 4,903 use only standard
Lean axioms or none, and 62 additionally use the existing Arc pointer contract.
All seven declarations in `Tree.Tuple.Comparison`, including its generated
equation theorem, are standard-only. The model dependency gate still passes
for 42 roots and 151 local model declarations. No new axiom, admission,
production Rust change, extraction change, or Aeneas source change is introduced.
The actual progressive update path supplies no optional hash map, so this
generic model correction does not establish a defect in its public proofs.
Borrowed CoW and the remaining hypothesis/model-fidelity audit remain open.

Initial model-dependency checkpoint (through `07ef38d`): the full library build
passes (2,023 jobs). All 42 available included roots pass the dependency audit,
with 151 referenced local model declarations across seven modules. No closure
references the older `List::intra_rebase` identity model, hash-map/hasher models,
or SmallVec models. Eight deliberately invalid inventories are rejected,
including a root outside the generated module and a local model replacing a
milhouse implementation. External model comments now state their restricted
domains; their definition bodies are unchanged. This checkpoint introduces
audit tooling and documentation only, with no proof, Rust, extraction, or
Aeneas change. At that checkpoint, the last complete axiom/import audit was the
4,958-declaration constructor checkpoint below. Model fidelity and minimal
hypotheses are not established by dependency closure alone, and borrowed CoW
remains unproved.

Previous constructor-reflection checkpoint (through `ed766a4`): the builder
trace, tree/list construction trace, and public success-condition focused
builds pass. The full library build passes (2,023 jobs), and the complete
axiom/import audit covers 4,958 theorem declarations across all 307 `Tree`
library modules. Of these, 4,896 use only standard Lean axioms or none; 62
additionally use the existing Arc pointer contract. All 24 declarations in the
four new modules use only standard Lean axioms or none. No admission, native
evaluation, new external axiom, Rust change, extraction change, external-model
change, or Aeneas source change is introduced. All 74 list/iterator proof
references in the API inventory resolve in the audited environment.

Successful construction now reflects the actual finite iterator sequence,
stored contents, exact count, and default map. Public success criteria for
iterator and vector constructors and both conversion traits prove the input,
capacity, and default-map conditions necessary and sufficient without assumed
iterator finiteness or default-map success. The existing finite-input total
contracts continue to build. The remaining assumption/model-fidelity audit
and borrowed CoW obligations stay open; Debug/Serde are excluded and TreeHash
is deferred under the revised scope.

### Historical validation checkpoints

The following checkpoints record progress and scope at the time they were
written. Their references to Debug, Serde/context protocols, TreeHash, or an
active goal are historical; the current [goal and scope](#goal-and-scope)
supersedes those scope statements. Excluded or deferred implementations do
not count as remaining work.

Previous empty-input premise checkpoint (through `b41b66a`): the shared decoder
representation, fixed decoder/roundtrip, and variable decoder/roundtrip focused
builds pass. The full library build passes (2,019 jobs), and the complete
axiom/import audit covers 4,934 theorem declarations across all 303 `Tree`
library modules. Of these, 4,872 use only standard Lean axioms or none; 62
additionally use the existing Arc pointer contract. All seven changed decoder
modules use only standard Lean axioms or none. No admission, native evaluation,
new external axiom, Rust change, extraction change, external-model change, or
Aeneas source change is introduced. All 68 list/iterator proof references in
the API inventory resolve in the audited environment.

The eight canonical content, sequence, and total decoder contracts now omit
metadata and packing premises for empty contents, with fixed positivity and
capacity conditional as well. Both actual encode/decode roundtrip proofs also
omit decoder-only premises on the empty branch. The general trace and
canonical sequence specifications share the successful materialized-sequence
representation theorem. Theorem names are retained with weaker premise types;
all dependent callers build. The remaining assumption/model-fidelity audit and
borrowed CoW obligations are still open under the revised scope.

Previous SSZ reflection and success-criterion checkpoint (through `029fdc4`):
the streaming-trace, public-input, public-trace, and success-condition focused
builds pass. The full library build passes (2,019 jobs), and the complete
axiom/import audit covers 4,933 theorem declarations across all 303 `Tree`
library modules. Of these, 4,871 use only standard Lean axioms or none; 62
additionally use the existing Arc pointer contract. The new/changed decoding
modules use only standard axioms. No admission, native evaluation, or new
external axiom is introduced. No Rust, extraction, external model, or Aeneas
source changed. The existing decoder specifications still build.

Successful decoding now determines its actual finite payload trace and exact
stored values/count and default map. The public theorem retains the connection
to input bytes through actual metadata and cursor initialization. Indexed
representation needs only the default map's empty laws and packing layout for
nonempty input. Public success is equivalent to a complete input trace,
occupied-layer capacity, and successful default-map construction, with both
directions proved and no list/builder-success premise. All 67 list/iterator
proof references in the API inventory resolve in the audited environment.
Borrowed CoW and the remaining assumption/model-fidelity audits stay open;
Debug and Serde are excluded and TreeHash is deferred under the revised scope.

Previous successful-payload and source-inventory checkpoint (through `0ed21ba`):
the generic cursor, fixed public decoder, and variable public decoder focused
builds pass. The full library build passes (2,015 jobs), and the complete
axiom/import audit covers 4,917 theorem declarations across all 299 `Tree`
library modules. Of these, 4,855 use only standard Lean axioms or none; 62
additionally use the existing Arc pointer contract. All three new modules use
only standard axioms. No admission, native evaluation, or new external axiom
is introduced. No Rust, extraction, external model, or Aeneas source changed.

The new successful-decoding contracts permit distinct accepted payloads for
equal values in both formats and a short final fixed chunk accepted by the
element decoder. They derive actual parsing and construction, with metadata
and layout laws omitted for empty input. The source inventory accounts for
all 19 inherent methods; its 64 list/iterator theorem references were checked
against the built environment. Both iterator Debug implementations are
explicitly accounted for, without a new extraction claim. Under the revised
scope, borrowed CoW and the remaining hypothesis/model-fidelity audits remain
open. Debug and Serde implementations, including in-place and context
deserialization, are out of scope; TreeHash and its shared-cache writes are
deferred for now.

Previous front-removal clone checkpoint (through `e06f464`): all focused
streaming, public clone-result, success-condition, and totality builds pass.
The full library build passes (2,012 jobs), and the complete axiom/import audit
covers 4,896 theorem declarations across all 296 `Tree` library modules.
Of these, 4,834 use only standard Lean axioms or none; 62 additionally use the
existing Arc pointer contract. The four new modules use only standard axioms.
The earlier public contracts retain their signatures; duplicate proofs now
reuse the generalized clone-result theorems. No admission, native evaluation,
or new external axiom is introduced. No Rust, extraction, external model, or
Aeneas source changed.

Successful nonzero removal now determines the actual ordered retained clone
results without clone identity or default-map semantics. The total sequence
contract represents those actual results under terminating retained clones and
the relevant empty-default-map laws. Success for every count is characterized
by the zero no-op or the necessary and sufficient nonzero conditions: removal
bound, occupied retained capacity, retained clone success, and default-map
construction success. Layout and backing assumptions are needed only when
rebuilding is reached. Full hashing/shared-cache effects, borrowed CoW, Debug,
Serde including default in-place deserialization, context deserialization, and
the remaining API/hypothesis audit remain outstanding.

Previous collection-clone checkpoint (through `c189a30`): the loop, finite-list
clone helpers, public outcome equations, and totality focused builds pass.
The full library build passes (2,008 jobs), and the complete axiom/import audit
covers 4,898 theorem declarations across all 292 `Tree` library modules.
Of these, 4,836 use only standard Lean axioms or none; 62 additionally use the
existing Arc pointer contract. All collection proofs use only standard axioms.
No admission, native evaluation, or new external axiom is introduced. No Rust,
extraction, external model, or Aeneas source changed.

Collection now has exact equations for arbitrary clone behavior, including
changed output values, failures, and divergence. Successful termination of
clones of represented values is necessary and sufficient for collection
success under the existing representation, backing, and layout invariants.
The total contract preserves sequence length without clone identity; the
original exact-contents contracts retain their signatures and follow as
specializations. Full hashing and shared-cache effects, borrowed CoW, Debug,
Serde including default in-place deserialization, context deserialization, and
the remaining API/hypothesis audit remain outstanding.

Previous front-removal capacity checkpoint (through `90acf16`): all focused
streaming, public totality, count, capacity, and zero-branch builds pass. The
full library build passes (2,005 jobs), and the complete axiom/import audit
covers 4,883 theorem declarations across all 289 `Tree` library modules.
Of these, 4,821 use only standard Lean axioms or none; 62 additionally use the
existing Arc pointer contract. The four new modules use only standard axioms.
No admission, native evaluation, or new external axiom is introduced. No Rust,
extraction, external model, or Aeneas source changed.

Nonzero removal success and retained counts no longer require clone identity
or default-map semantics. Occupied retained capacity is now proved necessary
and sufficient under terminating retained clones and default construction;
full sequence agreement continues to require the relevant identity and
empty-map laws. The successful-result preservation contracts now omit those
rebuilding laws on zero removal. The outstanding public API and extraction
work remains open.

Previous iterator-bounds and emptiness checkpoint (through `2e45792`): the
read-only constructor, CoW constructor/cache, and emptiness focused builds
pass. The full library build passes (2,001 jobs), and the complete axiom/import
audit covers 4,868 theorem declarations across all 285 `Tree` library modules.
Of these, 4,806 use only standard Lean axioms or none; 62 additionally use the
existing Arc pointer contract. The bounds and emptiness modules use only
standard axioms. No admission, native evaluation, or new external axiom is
introduced. No Rust, extraction, external model, or Aeneas source changed.

Oversized iterator starts now need no full sequence representation: actual
optional maximum metadata and the numeric comparison suffice, and the length
call is derived internally. Every returned constructor error is characterized;
CoW errors exactly match read-only errors and restore the original list through
every continuation input. `is_empty` has an exact total metadata specification,
a necessary-and-sufficient success condition, and a premise-free characterization
of returning true. The outstanding API and extraction work remains unchanged.

Previous total-append checkpoint (through `647da9b`): all three new push modules
pass their focused builds. The full library build passes (1,998 jobs), and
the complete axiom/import audit covers 4,853 theorem declarations across all
282 `Tree` library modules. Of these, 4,791 use only standard Lean axioms or
none; 62 additionally use the existing Arc pointer contract. All four new
public push theorems and their generated proof declarations use only standard
axioms. No admission, native evaluation, or new external axiom is introduced.
No Rust, extraction, external model, or Aeneas source changed.

The ordinary Serde source audit confirms that the actual visitor reaches the
recursive deserializer/visitor/sequence interface already documented in
UPSTREAM_BUGS issues 20 and 22; no equivalent failed extraction was rerun.
The public default `Deserialize::deserialize_in_place` is now explicitly
included in the pending coverage. Its assignment depends on successful
ordinary deserialization and cannot be counted as proved while that operation
remains unsupported.

Previous application-hypothesis checkpoint (through `55ac065`): both focused
application builds pass (1,810 jobs each), and the full library build passes
(1,995 jobs). The complete axiom/import audit still covers 4,838 theorem
declarations across all 279 `Tree` library modules: 4,776 use only standard
Lean axioms or none, and 62 additionally use the existing Arc pointer contract.
No admission, native evaluation, or new external axiom is introduced. The
successful application contracts now omit rebuilding/default-map laws on the
empty branch, matching the existing total contracts. No Rust, extraction,
external model, or Aeneas source changed.

Previous metadata and branch-hypothesis checkpoint (through `bc81415`): the
full Lean build passes (1,995 jobs), and the complete axiom/import audit covers
4,838 theorem declarations across all 279 `Tree` library modules. Of these,
4,776 use only standard Lean axioms or none; 62 also use the existing Arc
pointer contract. No admission, native evaluation, or new external axiom is
introduced. No Rust, extraction, external model, or Aeneas source changed.

The public length observer now has total and necessary/sufficient success
specifications from the actual map maximum, without representation or reads.
Fixed-width encoding length no longer requires indexed sequence agreement;
its complete total contract derives the actual length call internally and
proves both remaining arithmetic bounds necessary and sufficient. This keeps
the successor check even at zero width, matching Rust's evaluation order.
The `pop_front` total contract now omits packing layout on zero removal while
retaining its full contents and backing conclusions.

The full ProgressiveList goal remains active: actual root hashing/shared cache
effects, borrowed CoW methods and stepping, general Debug, Serde/context
protocols, and the remaining API and hypothesis audit are still outstanding.

Previous full-library axiom checkpoint (through `ff6d1bc`): the full Lean build
passes (1,994 jobs), and all 278 modules of the `Tree` library are included.
The environment audit covers 4,829 theorem declarations, including private
and generated proofs. Of these, 4,767 use only standard Lean axioms or none;
62 also use the existing `triomphe.arc.Arc.ptr_eq_spec`. No audited theorem
depends on an admission, native evaluation, or another external axiom. The
existing `core.mem.size_of.usize_spec` is declared but unused by these theorems.
Only those two documented external axiom declarations remain in the library.

The initial complete audit found two `native_decide` axioms affecting seven
declarations in `Tree/Repeat.lean`, including `repeat_list_returns_dense`.
Commit `561a68f` replaces both arithmetic evaluations with kernel-checked
platform-width proofs and removes those dependencies without new premises.
The reusable audit accepted the resulting inventory and rejected four negative
cases: the actual former native dependency, a missing proof module, a truncated
inventory, and an additional axiom declaration. No Rust, extraction, external
model, or Aeneas source changed at this checkpoint.

The full ProgressiveList goal remains active. The axiom/import gate is now
complete for the current library; actual root hashing/shared cache effects,
borrowed CoW methods and stepping, general Debug, Serde/context protocols,
and the remaining API and hypothesis audit are still outstanding.

Previous clone-from checkpoint (through `b0e66b5`): fresh Charon/Aeneas
extraction and the full Lean build pass (1,994 jobs), with all 278 project
modules reachable from `Tree`, excluding external templates. All eight new
`clone_from` results and the eight existing Clone results were audited and use
only standard Lean axioms or none. The new caller passes Rust formatting checks
and is compiled by Charon only under `cfg(milhouse_aeneas)`; production Rust
behavior is unchanged. No admissions, external axioms, new extraction
postprocessing, external model changes, or Aeneas changes were introduced.

The inherited `Clone::clone_from` is now an explicitly covered public entry
point. Its actual generated dictionary uses the existing standard default,
and the proof connects the emitted Rust caller to that method. Total source
replacement needs source representation/backing validity and only the actual
source map clone's termination and read/maximum laws. No destination invariant,
element cloning, packing, or pending-map `clone_from` law is required. Exact
source backing fields, source caches, and the pending observer are also covered.

The full ProgressiveList goal remains active: actual root hashing/shared cache
effects, borrowed CoW methods and stepping, general Debug, Serde/context
protocols, and the remaining API/assumption audit are still outstanding.

Previous clone totality checkpoint (through `0c1fc50`): the full Lean build
passes (1,993 jobs), with all 277 project modules reachable from `Tree`,
excluding external templates. All eight public clone results, including the
new success equivalence and total specification, were audited and use only
standard Lean axioms or none. No admissions, external axioms, Rust changes,
extraction changes, external model changes, or Aeneas changes were introduced.

Clone now has a complete total sequence/backing contract derived from the
actual pending-map clone's termination and read/maximum preservation. Its
exact backing-field preservation also retains the existing cache invariants.
The success equivalence separately requires no representation or semantic
map law and identifies the precise external termination obligation.

The full ProgressiveList goal remains active: actual root hashing/shared cache
effects, borrowed CoW methods and stepping, general Debug, Serde/context
protocols, and the remaining API/assumption audit are still outstanding.

Previous packed rebase soundness checkpoint (through `40855b5`): the full Lean
build passes (1,992 jobs), with all 276 project modules reachable from `Tree`,
excluding external templates. The 59-result rebase audit includes the new
finite-pair scope conversion, consolidated vector contents result, and the
binary/progressive/public operational contracts. Thirty use only standard
Lean axioms or none; 29 also use the existing `triomphe.arc.Arc.ptr_eq_spec`.
No admissions, new axioms, Rust changes, extraction changes, external model
changes, or Aeneas changes were introduced.

The packed branch of `RebaseEqualitySound` now uses `NeOn` with `NeSoundAt`,
omitting element laws after the first true `ne`. All existing public rebase
contents and cache contracts retain their conclusions under this weaker
scope. The vector bridge also replaces its global law with the reached-pair
scope, and the duplicated vector induction and intermediate bridge are removed.
Laws on all supplied pairs remain sufficient through `NeOn.of_pairs`.

The full ProgressiveList goal remains active: actual root hashing/shared cache
effects, borrowed CoW methods and stepping, general Debug, Serde/context
protocols, and the remaining API/assumption audit are still outstanding.

Previous equality input-scope checkpoint (through `f5ad99a`): the full Lean
build passes (1,992 jobs), with all 276 project modules reachable from `Tree`,
excluding external templates. The 31-result equality audit covers all new
scope, element-soundness, and pointer lemmas, the affected public operational
contracts, and the unconditional list comparison characterization. Seventeen
use only standard Lean axioms or none; 14 also use the existing
`triomphe.arc.Arc.ptr_eq_spec`. No admissions, new axioms, Rust changes,
extraction changes, external model changes, or Aeneas changes were introduced.

Binary-tree, progressive-tree, and public list equality now require element
laws only for selected input branches. Total correctness uses `NeSpecAt`;
positive-result soundness and representation transfer use only `NeSoundAt`.
Pointer shortcuts, packed length rejection, left-to-right field comparison,
and packed element short circuiting prune the scopes. Uniform laws remain
sufficient through conversion helpers, but are no longer public operation
premises. Shared-backing list equality additionally has an exact computation
equation preserving pending-map failure/divergence without any element law.

A fresh fetch confirms that `origin/main` remains `d67aabd`, already included
through merge commit `473f5c8`; there are no unresolved conflicts. The full
build above validates the existing proofs together with this equality work.
The full ProgressiveList goal remains active: actual root hashing/shared cache
effects, borrowed CoW methods and stepping, general Debug, Serde/context
protocols, and the remaining API/assumption audit are still outstanding.

Previous reached-comparison checkpoint (through `429cd99`): the full Lean
build passes (1,987 jobs), with all 271 project modules reachable from `Tree`,
excluding external templates. All five new public lemmas and the affected
rebase interfaces were included in a 57-result axiom audit. Twenty-eight use
only standard Lean axioms; 29 also use the existing
`triomphe.arc.Arc.ptr_eq_spec`. No admissions, new axioms, Rust changes,
extraction changes, external model changes, or Aeneas changes were introduced.

Rebase termination assumptions now follow actual supplied optional lengths,
full depth, pointer shortcuts, hash shortcuts, and packed element short
circuiting. Both public success variants and all represented-sequence/cache
contracts inherit this refinement. The underlying binary/progressive success
results still need no density or recorded-length/content agreement; all child
and layer metadata are derived internally. Packed loop termination is both
sufficient for and recovered from the reached-element-call law.

This closes the previously recorded termination-scope refinement. The full
ProgressiveList goal remains active: actual root hashing/shared cache effects,
borrowed CoW methods and stepping, general Debug, Serde/context protocols, and
the remaining API/assumption audit are still outstanding.

Previous rebase shortcut-scope checkpoint (through `2a550d5`): the full Lean
build passes (1,984 jobs), with all 268 project modules reachable from `Tree`,
excluding external templates. The audit includes all 14 new public shortcut
lemmas and 37 affected operational/bridge results. Of those 51 lemmas, 22 use
only standard Lean axioms and 29 also use the existing
`triomphe.arc.Arc.ptr_eq_spec`; none uses an admission or new axiom. No Rust,
extraction, external model, or Aeneas source changed.

All recursive rebase law scopes now stop at pointer sharing. Equality and
collision scopes also stop at hash shortcuts, with only the selected binary
root contributing a collision input. Both full public rebase contents/cache
specifications inherit these weaker conditions. Exact public pointer-shortcut
results additionally need no structural or packing invariants, and the owning
variant preserves the actual pending-map clone's failure/divergence behavior.
The generic success proof's comparison-termination scope still requires
refinement below hash shortcuts using actual supplied length metadata; its
current pointer pruning does not discharge that separate obligation.

The full goal remains active. Actual root hashing/shared cache effects,
borrowed CoW methods and stepping, general Debug, Serde/context protocols,
and the remaining assumption audit are not established by this checkpoint.

Previous rebase equality-scope checkpoint (through `46963ab`): the full Lean
build passes (1,979 jobs), with all 263 project modules reachable from the
`Tree.lean` root, excluding external templates. All four new public helpers
and all 21 updated operational specifications were audited. Three helpers
use only standard Lean axioms; the Arc helper and 21 operational results also
use the existing `triomphe.arc.Arc.ptr_eq_spec`. No admissions, new axioms,
production Rust changes, extraction changes, or external model changes were
introduced. Public rebase contracts no longer require global element
soundness: only corresponding leaf pairs, guarded by actual pointer shortcuts
and packed-vector length checks, need the appropriate `eq` or `ne` law.

The standalone shared-cache reproducer (`08a96a5`) passes its native Rust
write-visibility test and formatting check. It records that current Aeneas
translation drops the write argument and reuses a pre-write read guard, even
with `-eval-drops`. This narrows the hashing blocker: a different pure local
lock model cannot restore the missing dependence on the written value. The
fixture is separate from the proof library; Aeneas remains unchanged. Actual
root hashing and shared cache effects, borrowed CoW operations and iterator
stepping, general Debug, Serde/context protocols, and the remaining assumption
audit are still outstanding. This checkpoint does not establish complete
ProgressiveList correctness.

Previous mutation and rebase validity checkpoint (through `d3a3795`): the full
Lean build passes (1,977 jobs), including all earlier proofs and five new
modules. All 261 project proof modules are reachable from `Tree`. All 22 new
public lemmas were audited: 15 use only `propext`, `Classical.choice`, and
`Quot.sound`; seven operational public rebase lemmas additionally use the
existing `triomphe.arc.Arc.ptr_eq_spec` axiom. None uses `sorryAx` or a new axiom.
The mutation proofs and finite reference-collision bridges themselves do not
use the Arc pointer-equality axiom.

Backing cache predicates now survive all currently extracted pending-mutation,
clone, and CoW constructor continuation paths. The rebase bridge derives the
operational hash-shortcut law from valid caches and reference collision
soundness on finite corresponding binary inputs, with original zero-cache
nodes omitted and no progressive-cache comparison premise. Both public
rebase variants have complete total reference-cache specifications, and
cleared original caches discharge every collision obligation internally.

This checkpoint changes only Lean proofs, specifications, imports, and this
record. No Rust, generated extraction, external model, or Aeneas source changed.
Actual semantic root computation and shared cache writes remain outstanding,
along with the borrowed CoW/iterator, Debug, and generic/context serialization
extraction and protocol gaps. The full goal is still active.

Previous constructor and reconstruction cache checkpoint (through `26a1117`):
the full Lean build passes (1,972 jobs), including all earlier proofs and ten
new modules. All 256 project proof modules are reachable from `Tree`. All 35
new public lemmas were audited and depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none uses `sorryAx`, a new axiom, or the
Arc pointer-equality axiom.

The actual binary/progressive builder chain now establishes cleared caches
through pushes, packed-leaf extension, merges, padding, rollover, iterator
consumption, and final spine assembly. Public iterator/vector construction,
both conversion traits, empty/default, SSZ decoding, and arbitrary generation
initialize cleared caches. Nonzero front removal rebuilds cleared caches
without an assumption about the old caches; all returned front-removal states
preserve cache validity. Successful initialization requires no element-hashing,
packing, map, clone, iterator-output, or finiteness laws. The four total
constructor specifications retain exactly their prior operational premises and
derive reference cache validity internally.

This checkpoint changes only Lean proofs, specifications, imports, and this
record. No Rust, generated extraction, external model, or Aeneas source changed.
Cache preservation through remaining mutations, semantic root computation,
shared cache writes, and the collision-soundness bridge to rebasing still need
work. Borrowed CoW, Debug, and generic/context serialization extraction gaps
also remain. The full goal is still active.

Earlier constructor cache foundation checkpoint: `Tree/HashCache/Cleared.lean`
defines cleared caches independently of tree shape and depth, and proves
that they satisfy every cache predicate accepting the zero sentinel.
`Tree/Builder/Caches/Basic.lean` tracks cleared caches across forest pushes
and pops and proves clearing for fresh leaves, packed singletons, nodes,
and successful `Builder.new` calls. No element-hashing, packing-layout,
or arithmetic laws are required. At that checkpoint, preservation through
builder push/finish and public constructors remained outstanding.

The full Lean build passes (1,962 jobs), with all 246 project proof modules
reachable from `Tree`. All eight new lemmas depend only on `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` dependencies.
Fetching `origin/main` confirms `d67aabd` is already included through merge
commit `473f5c8`; there are no remaining merge conflicts. This checkpoint
changes only Lean proofs, imports, and this validation record.

Previous apply-updates cache checkpoint (through `7848beb`): the full Lean
build passes (1,960 jobs), including all earlier proofs and five new modules.
All seven new lemmas were audited and depend only on `propext`,
`Classical.choice`, and `Quot.sound`; there are no new axioms or `sorryAx`
dependencies. The cache-preservation chain does not require the Arc
pointer-equality axiom.

Cache validity now survives the actual binary and progressive update
recursion and public `apply_updates`, including Rust-error restoration. The
successful-execution invariant needs only valid input caches and acceptance
of the zero sentinel. It introduces no shape, packing, alignment, clone,
map-semantic, maximum, capacity, or termination premises. Specialization to a
mathematical reference hash supplies zero validity by definition. The total
public result adds only the input cache invariant to the existing total
sequence/backing/pending-update contract, retaining all its branch and query
scoping.

This checkpoint changes only Lean proofs, specifications, and imports; no
Rust, generated extraction, external model, or Aeneas source changed. Cache
initialization through constructors, preservation through remaining mutations,
semantic root computation, shared cache writes, and the collision-soundness
bridge to rebasing still need work. Borrowed CoW, Debug, and generic/context
serialization extraction gaps also remain. The full goal is still active.

Previous packed-cache checkpoint (through `5bdf22f`): fresh production
extraction, the full Lean build (1,955 jobs), formatting, and all 331 Rust
release tests with `arbitrary` pass. The regression for hashing a packed leaf
before pushing reproduced the stale-root bug before the one-line fix.
The two new tests cover repeated hash-then-push calls and full-leaf rejection
with a populated cache. The generated diff contains only the corresponding
push body and source location; no external interface or Aeneas change is
needed.

All eight new cache/state lemmas and the three adjusted packed-push/builder
lemmas were audited: all eleven use only `propext`, `Classical.choice`, and
`Quot.sound`. The cache proofs need neither clone identity nor map laws,
alignment, or termination assumptions. The full build includes all earlier
proofs and both new modules through the root `Tree` target.

This establishes packed mutation invalidation and fixes an actual stale
cache, but does not yet establish semantic cache validity through all list
construction/mutation operations or prove root hash computation. Borrowed CoW,
Debug, serialization/context protocols, and faithful shared cache writes also
remain unfinished. The full ProgressiveList goal remains active.

Previous cache-preservation checkpoint (through `e34a94c`): the full Lean build
passes (1,953 jobs), including all earlier proofs and the six new modules.
All nine new lemmas were audited. The action-combination and binary-cache
projection lemmas use only standard Lean axioms; the seven operational
binary/progressive/public results additionally use the existing trusted
`triomphe.arc.Arc.ptr_eq_spec`. None depends on `sorryAx` or a new axiom.

The two public total specifications combine successful rebasing, represented
sequence preservation, backing validity, exact length, pending-map behavior,
and cache-invariant preservation. Successful-execution cache specifications
need no pending-map clone/read/maximum law. Cache predicates retain both the
logical contents and binary/progressive depth; base progressive caches are
unconstrained because they are never imported. All child executions and their
content-preservation facts are derived from the actual extracted code.

The Debug diagnosis is recorded in UPSTREAM_BUGS issue 5: resolving recursive
dictionary references alone cannot supply missing general formatter or lock
observation semantics. No Rust, generated extraction, external-model, or Aeneas
source change is included in this checkpoint. Borrowed CoW, full Debug,
serialization/context protocols, semantic root hashing and shared cache writes,
and construction/mutation establishment of semantic cache validity remain
unfinished. The full ProgressiveList objective is still active.

Previous range-answer correctness checkpoint (through `b19d342`): the full Lean
build passes (1,947 jobs). Four local-law/scope conversion lemmas, seven binary
content/density/success specifications, six progressive range/layer bridges,
two progressive content specifications, three progressive density
specifications, two progressive success specifications, and eight public list
specifications were audited. All 32 use only `propext`, `Classical.choice`,
and `Quot.sound` (or subsets, including two with no axioms). Logs are
`/tmp/milhouse-apply-updates-range-answer-final-build.log`,
`/tmp/milhouse-range-answer-scope-audit.log`,
`/tmp/milhouse-binary-range-answer-audit.log`,
`/tmp/milhouse-progressive-range-answer-bridges-audit.log`,
`/tmp/milhouse-progressive-range-answer-contents-audit.log`,
`/tmp/milhouse-progressive-range-answer-density-audit.log`,
`/tmp/milhouse-progressive-range-answer-success-audit.log`, and
`/tmp/milhouse-apply-updates-range-answer-audit.log`.

Range-answer correctness no longer requires a law for arbitrary endpoint
pairs anywhere in the binary/progressive/public apply-updates proof chain.
Each induction consumes the current queried law and carries descendant laws
only under the actual selection guard. The public scope is tied to the
maximum actually read; total empty application retains its no-work branch.
The unrestricted range-law definitions remain available for external map
instances and compatibility. No Rust, extraction, external-model, or Aeneas
source changed. The full goal remains open: the wider premise audit, borrowed
CoW extraction, semantic hashing/cache validity, serialization/deserialization,
Debug, and every pending operation-coverage row still need work.

Previous range-termination checkpoint (through `5a40c32`): the full Lean build
passes (1,947 jobs), with all 230 project modules reachable from `Tree`.
Seven binary query-scope helpers, six progressive query-scope helpers, three
binary success/total specifications, two progressive success specifications,
and four public list success/total/capacity specifications were audited. All
22 use only `propext`, `Classical.choice`, and `Quot.sound` (or subsets).
The build and audit logs are
`/tmp/milhouse-apply-updates-range-final-build.log`,
`/tmp/milhouse-binary-range-scope-audit.log`,
`/tmp/milhouse-progressive-range-scope-audit.log`,
`/tmp/milhouse-binary-range-success-audit.log`,
`/tmp/milhouse-progressive-range-success-audit.log`, and
`/tmp/milhouse-apply-updates-range-audit.log`.

Public total application no longer assumes terminating range queries for
arbitrary endpoints. Termination is required at the reached layer queries and
selected binary queries for the maximum actually read, conditional on a
nonempty pending map. Every recursive success proof carries this restriction;
no successful internal update is assumed. No Rust, extraction, external-model,
or Aeneas source changed. Range-answer correctness still had broad domains at
that checkpoint; the later checkpoint above completes that restriction. The
remaining assumption audit, borrowed CoW extraction, semantic hashing/cache
validity, serialization/deserialization, Debug, and pending coverage rows are
not discharged by either checkpoint.

Previous retained-value clone checkpoint (through `6f48984`): the full Lean
build passes (1,945 jobs), with all 228 project modules reachable from `Tree`.
Two vector-clone lemmas, three queried-slot scan/update lemmas, four packed
content/total lemmas, eleven binary-scope helpers, four binary specifications,
fourteen progressive-scope helpers, six progressive content/layer lemmas, and
six public list specifications were audited. All 50 depend only on `propext`,
`Classical.choice`, and `Quot.sound` (or subsets). Build and audit logs are
`/tmp/milhouse-apply-updates-retained-final-build.log`,
`/tmp/milhouse-vec-clone-audit.log`,
`/tmp/milhouse-packed-query-clone-audit.log`,
`/tmp/milhouse-packed-retained-total-audit.log`,
`/tmp/milhouse-binary-retained-scope-audit.log`,
`/tmp/milhouse-binary-retained-contents-audit.log`,
`/tmp/milhouse-progressive-retained-scope-audit.log`,
`/tmp/milhouse-progressive-retained-contents-audit.log`, and
`/tmp/milhouse-apply-updates-retained-audit.log`.

The packed, binary, progressive, and public list specifications now require
identity only for retained stored slots and selected pending values. Rust
clones packed storage before overwriting it, so discarded copies still need
termination for total correctness. This distinction is carried through actual
recursive calls to the public `apply_updates_total_spec`; it is not confined
to a leaf helper. No Rust, extraction, external-model, or Aeneas source changed.
The full goal remains open: the broader premise audit (including the domains
of external range-query laws), borrowed CoW extraction, semantic hashing/cache
validity, serialization/deserialization, Debug, and every pending coverage row
still need work.

Previous public apply-updates clone-scope checkpoint (through `e5f33d3`): the
full Lean build passes (1,944 jobs). Six progressive-scope helpers, two
progressive contents lemmas, two progressive success lemmas, and six public
list specifications were audited; all 16 use only `propext`, `Classical.choice`,
and `Quot.sound`. The new scope module is included by `Tree.lean`. Logs are
`/tmp/milhouse-apply-updates-scoped-final-build.log`,
`/tmp/milhouse-progressive-clone-scope-audit.log`,
`/tmp/milhouse-progressive-contents-scoped-audit.log`,
`/tmp/milhouse-progressive-success-scoped-audit.log`, and
`/tmp/milhouse-apply-updates-scoped-audit.log`. No Rust, extraction, external
model, or Aeneas source changed.

That checkpoint removed global element-clone laws from the binary, progressive,
and public list proof chain. Identity for copied stored values subsequently
overwritten remained to be removed; the retained-value checkpoint above now
completes that refinement. The broader assumption and coverage audits remain
open.

Previous recursive clone-scope checkpoint (through `2c55621`): the full Lean
build passes (1,943 jobs), including every earlier proof. Four clone-scope
foundations, three binary contents/lookup lemmas, three binary success/totality
lemmas, and four progressive-layer lemmas were audited; all 14 depend only
on `propext`, `Classical.choice`, and `Quot.sound`. The root `Tree` target
includes the new scope module. The full build log is
`/tmp/milhouse-bulk-recursive-clone-final-build.log`; audit logs are
`/tmp/milhouse-bulk-clone-scope-audit.log`,
`/tmp/milhouse-bulk-contents-scoped-audit.log`,
`/tmp/milhouse-bulk-success-scoped-audit.log`, and
`/tmp/milhouse-progressive-layer-scoped-audit.log`. No Rust, generated
extraction, external-model, or Aeneas source changed.

At that checkpoint, the binary recursions and progressive layer bridges no
longer required cloning laws for arbitrary element values or skipped subtrees.
Progressive-spine and public `apply_updates` clone scoping remained to be
propagated; the later checkpoint above completes that propagation. Neither
checkpoint discharges borrowed CoW extraction,
semantic hashing/cache validity, serialization/deserialization, Debug, or any
other pending public-operation obligation in the coverage table.

Previous clone-scope foundation checkpoint (through `f3112b4`): the full Lean
build passes (1,942 jobs), including all earlier mutable-access and public
apply-updates proofs. The new actual-clone leaf theorem, the two strengthened
unpacked-leaf theorems, and the strengthened packed offset bridge were audited
together; all four depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Logs are `/tmp/milhouse-mutable-bulk-scoped-final-build.log` and
`/tmp/milhouse-bulk-leaf-clone-audit.log`. No Rust, extraction, model, or Aeneas
source changed. These leaf-level results are foundations for removing global
clone assumptions from the recursive specifications, not completion of that
remaining obligation.

Previous mutable-access checkpoint (through `77a778d`): the full Lean build
passes (1,942 jobs). The four read lemmas completed in `6b08cbd` and the three
new success/replacement lemmas were audited together; each depends only on
`propext`, `Classical.choice`, and `Quot.sound`. No admission, native-evaluation,
or Arc pointer axiom is inherited. The new module is included by `Tree.lean`.
The in-bounds and all-index specifications require no identity-clone or
structural-backing premise. No production Rust, extraction, external model,
or Aeneas source changed, so the consuming-CoW extraction and Rust-test
checkpoint below remains applicable. Build and audit logs are
`/tmp/milhouse-mutable-total-final-build.log` and
`/tmp/milhouse-mutable-total-audit.log`.

The separate borrowed-CoW probes in
`/tmp/milhouse-cow-borrowed-probe-z1n008ka/` reproduce the dereference,
borrowed-mutation, and iterator-step failures even after removing inner trait
dispatch, recursion, closures, and result/option adapters where applicable.
The precise loan-lookup and backward-projection diagnostics are recorded in
UPSTREAM_BUGS issues 9 and 16. No failing rewrite or partial generated body is
retained in the production proof boundary. These methods, semantic hashing
and cache validity, serialization/deserialization, Debug, and every other
pending coverage row remain in the full goal. At that checkpoint, binary and
progressive bulk-update and public apply-updates proofs still exposed global
clone laws. The later recursive clone-scope checkpoint above narrows the binary
recursions and progressive-layer bridges; the subsequent public apply-updates
checkpoint carries the scope through the spine and list callers.

Previous consuming-CoW checkpoint (through `f71c774`): complete extraction and
the full Lean build pass (1,941 jobs), including every earlier proof. All nine
new public entry, handle, and list replacement lemmas were audited together;
their only axioms are `propext`, `Classical.choice`, and `Quot.sound` (or
subsets), with no admission, native-evaluation, or Arc pointer dependency.
The new modules are included by the root `Tree` target. All 329 release tests
with `arbitrary` pass, including three new consuming protocol tests covering
both map implementations, a nonidentity clone and exact clone count, occupied
handles, missing entries, and maximum-index state. Formatting and diff checks
pass. Rust changes are confined to concrete consuming helpers, equivalent
explicit result/entry matches, a proof caller, and the protocol tests. External
vacant-entry models now preserve insertion write-back state and vector growth;
Aeneas sources are unchanged. The full goal still includes borrowed CoW
dereferencing/mutation and iterator stepping, semantic hashing/cache validity,
serialization/deserialization, Debug, and every other pending coverage row.

Previous rebase totality checkpoint: the full Lean build passes (1,936 jobs),
including all earlier proofs and the completed former `Success.lean` draft.
All 15 public lemmas added since the TreeHash checkpoint were audited
together. Arithmetic, vector comparison, comparison-law lifting, and
nonmutating metadata/observer lemmas use only standard Lean axioms. The eight
pointer-dependent comparison/success/content results additionally use the
existing trusted `triomphe.arc.Arc.ptr_eq_spec`; none inherits an admission or
native-evaluation axiom. Existing upstream Slice/StringIter admissions and
lint warnings remain in the build output. All new modules are imported by
the root `Tree` target. This checkpoint changes only Lean proofs and their
documentation; Rust, generated extraction, external models, and Aeneas sources
are unchanged. Semantic hashing/cache obligations, CoW stepping and
materialization, serialization/deserialization protocols, Debug, and every
other pending coverage row remain part of the full objective.

Previous TreeHash metadata checkpoint: regenerated extraction and the full
Lean build pass (1,931 jobs), including all earlier proofs. The three new public
classification and packing-rejection lemmas use only `propext`,
`Classical.choice`, and `Quot.sound`. Formatting passes; production Rust and
external models are unchanged. The fresh root probe confirms the translation
and shared-cache limitations in UPSTREAM_BUGS issue 21. Root hashing, its
pending-update assertion, maintained semantic cache invariants, and every
other pending API row remain in the full objective.

Previous Arbitrary checkpoint (through `5940d7b`): the full Lean build passes
(1,930 jobs), including every earlier proof and all new modules through the
root `Tree` import. All 26 new public control, trace, list-generation,
capacity-characterization, and trait-default lemmas were audited together;
their only axioms are `propext`, `Classical.choice`, and `Quot.sound` (or
subsets). No new lemma inherits an admission, native-evaluation axiom, or Arc
pointer axiom. Existing upstream Slice/StringIter admissions and lint warnings
remain in the build output.

The complete extraction was regenerated with `arbitrary` enabled, using the
actual ProgressiveList method and extraction-only trait callers. The external
Vec model follows pinned arbitrary 1.4.1. All 326 release tests pass with this
feature enabled, including four new protocol tests for stopping-byte
consumption, first-error state, custom input replacement, and list/Vec
agreement plus trait defaults across progressive layer boundaries. Formatting
passes. No production method or Aeneas source changed; a local qualification
postprocessor handles the generated trait's namespace shadowing (UPSTREAM_BUGS
issue 7). Serialization/deserialization, CoW stepping/materialization, Debug,
semantic hashing/cache invariants, context deserialization, and other remaining
coverage obligations above remain part of the full goal.

Previous apply-updates totality checkpoint (through `79534c8`): the full Lean
build passes (1,923 jobs), including every earlier proof. All 19 new public
insertion, packed/binary/progressive bulk-update, public application, and
capacity-characterization lemmas were audited together through the root
`Tree` import. Their only axioms are `propext`, `Classical.choice`, and
`Quot.sound`; none inherits admissions, native-evaluation axioms, or the Arc
pointer axiom. The existing upstream Slice/StringIter admissions and existing
lint warnings remain in the build output.

The actual public `apply_updates` now has a total sequence/backing/pending
specification. Its empty-map branch has no rebuilding premises. For a
nonempty map, representability of occupied final layers is an exact success
condition under terminating external calls and coherent range/maximum
metadata. The proofs derive all intermediate arithmetic, no-gap properties,
map lookup termination, and the recursion-bound maximum from the stated
invariants and representation. No Rust, extraction, external model, or Aeneas
source changed. Serialization/deserialization, CoW stepping/materialization,
Debug, semantic hashing/cache invariants, feature-specific APIs, and other
outstanding coverage obligations remain in the full goal.

Previous constructor/front-removal totality checkpoint (through `9663f44`):
the full Lean build passes (1,916 jobs). All 15 new public extension,
construction, capacity-characterization, and front-removal lemmas were audited
together through the root `Tree` import. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound` (or subsets), with no admissions,
native-evaluation axioms, or Arc pointer axiom.

The public constructors and conversions now prove success rather than assume
it. The occupied-layer condition is exact: with a finite iterator and a
successful default map, construction succeeds if and only if `LengthFits`
holds for the input length. Front removal has a total in-bounds specification;
zero removal needs no clone, suffix-capacity, or default-map law. All earlier
proofs remain included in the full build.

The Serde extraction probe in `3327944` produced a verified limitation: the
actual public serialization body is reached, but mutually recursive external
trait dictionaries fail Lean elaboration. The attempted generic dispatch
exclusion does not remove the cycle. A faithful external protocol model or
backend support remains for discussion; custom `collect_seq` overrides and
length-hint behavior must be preserved. No failed generated output or probe
root was retained, and no Rust, normal extraction, external models, or Aeneas
sources changed. Serialization/deserialization, CoW stepping/materialization,
Debug, semantic hashing/cache invariants, feature-specific APIs, and the
remaining obligations stated in the coverage rows remain in the full goal.

Previous arbitrary-payload-prefix checkpoint (through `0b3232d`): the full
Lean build passes (1,910 jobs), including all earlier proofs. All 16 new
public prefix, annotated-trace, and decoder-error results were audited together
through the root `Tree` import. They use only `propext`, `Classical.choice`, and
`Quot.sound` (or subsets), without admissions, native-evaluation axioms, or the
Arc pointer axiom.

Variable malformed-offset and element-error specifications now apply after
arbitrary successful prefixes, with exact check order and actual partial-builder
finalization. Both fixed and variable public error specifications support
per-entry payload bytes, including different accepted encodings of equal
values. No own-method success or canonical-encoding premise is exposed. The
fixed format bounds only capacities occupied by successfully decoded values;
variable capacity follows from the table. Empty variable payloads and short
fixed final chunks retain the element decoder's exact result.

No Rust, generated extraction, external models, or Aeneas sources changed.
Serialization/deserialization, CoW stepping/materialization, Debug, semantic
hashing/cache invariants, and feature-specific APIs remain in the full goal;
all API rows above retain their stated limits and obligations.

Previous malformed-SSZ checkpoint (through `7546b37`): the full Lean
build passes (1,902 jobs), including all existing proofs. All 19 new public
cursor, prefix, and decoder-error results were audited together through the
root `Tree` import. They use only `propext`, `Classical.choice`, and `Quot.sound`,
with no admissions, native-evaluation axioms, or Arc pointer axiom.

The actual public decoder now rejects malformed first offsets directly from
bytes, returns fixed-element errors after arbitrary successful prefixes, and
rejects malformed second offsets and a decreasing third offset with the exact
payload/error order. Generic error propagation through builder finalization is
proved for both formats. Variable cursor length bounds supply all prefix
capacity checks; fixed-input nonemptiness and bounds implied by other offsets
are derived rather than exposed as extra premises.

No Rust, generated extraction, external models, or Aeneas sources changed.
At that checkpoint, general variable malformed-input specifications after
arbitrary-length prefixes remained pending, alongside the other API work.

Previous SSZ totality and roundtrip checkpoint (through `47e0e56`): the full
Lean build passes (1,895 jobs), including all earlier proofs. All 14 new public
length-bound, streaming-success, decoder-totality, and roundtrip lemmas were
audited together and use only `propext`, `Classical.choice`, and `Quot.sound`
(or subsets), with no admissions, native-evaluation axioms, or Arc pointer
axiom. Both actual public decoding formats now have valid-input success and
sequence specifications; both actual owning encoding/decoding roundtrips
preserve the merged sequence and every indexed read, rebuild valid backing,
and clear pending updates. Streaming construction also terminates after the
first cursor or element error, retaining its decoded prefix and error.

`LengthFits` constrains only layers occupied by the final sequence. It supplies
all intermediate rollover bounds. Variable decoding derives it from the
four-byte-per-value offset table and the input slice's size bound, so it needs
no separate sequence-capacity premise. General fixed-width decoding retains
that condition, which is not implied by byte representability for every small
element width and packing layout. Roundtrips require element codec laws only
on represented values and fitting buffers; no clone law or assumed success
of a list operation is needed.

A fresh fetch of `origin/main` at `d67aabd` and an actual merge report that the
branch already includes main; there are no merge conflicts. No Rust, generated
extraction, external models, or Aeneas sources changed at this checkpoint.
Further malformed-input specifications, serialization, deserialization, CoW
stepping/materialization, Debug, semantic hashing/cache invariants, and
feature-specific APIs remain part of the full objective.

Previous builder-totality checkpoint (through `f759827`): the full Lean build
passes (1,888 jobs). Binary value insertion, progressive insertion including
rollover, complete binary finalization, and progressive finalization now have
total specifications. Binary finalization requires only its invariant;
progressive insertion requires next-layer representability only when rollover
occurs. All other depth, counter, vector, and arithmetic conditions are derived
internally. The finished binary and progressive trees retain their exact
sequences, recorded lengths, and structural invariants.

All 38 new or newly exposed lemmas since `bf270ae` were audited together through
the root `Tree` import: 30 new lemmas and eight exposed existing helpers use
only `propext`, `Classical.choice`, and `Quot.sound`. None inherits admissions,
native-evaluation axioms, or the Arc pointer axiom. The full build includes all
earlier decoding, encoding, iteration, mutation, equality, and rebase proofs.
No Rust, generated extraction, external models, or Aeneas sources changed.

At that checkpoint, remaining decoding work included deriving rollover bounds
across the complete input sequence, composing these total builder operations through the streaming
loop and public decoder, further malformed-input specifications, and full list
roundtrips. Serialization, deserialization, CoW stepping/materialization, Debug,
semantic hashing/cache invariants, and feature-specific APIs remain part of the
full objective.

Previous variable-decoding and builder-initialization checkpoint (through `2a59a23`):
the full Lean build passes (1,871 jobs). Both fixed- and variable-element public decoders now have
sequence-level partial correctness specifications, deriving actual cursor and
builder invariants internally. Canonical variable offsets identify every
payload, including empty payloads; exhausted cursors do not advance. Index and
offset arithmetic bounds follow from the input slice and table size. Only
offsets actually emitted require SSZ's 32-bit bound, with no additional bound
on the final payload end. `Tree/Builder/New.lean` proves binary builder
initialization succeeds from representable capacity, deriving its arithmetic
and depth checks. `Tree/ProgressiveTree/Builder/New.lean` proves initial
progressive builder success and the complete empty-state invariant from the
packing layout alone. All 16 new variable cursor/public decoder and builder
initialization lemmas were audited and use only `propext`, `Classical.choice`,
and `Quot.sound`.
The preceding fixed-decoding and streaming-construction proofs are included
in this full build, as is the canonical offset-reader bridge in `eb433d2`.
No Rust, generated extraction, external models, or Aeneas sources changed.
At that checkpoint, remaining decoding work included malformed-input specifications and
valid-input success/totality for full list roundtrips, including builder push
and finalization totality and their streaming-loop composition. Serialization,
deserialization, CoW stepping/materialization, Debug, semantic hashing/cache
invariants, and feature-specific APIs remain part of the full objective.

Previous encoding checkpoint (through `5ef4652`): all five SSZ `Encode` methods
are extracted and have metadata, exact length, and exact output specifications,
covering both fixed and variable element types. Fresh extraction and the full
Lean build pass (1,851 jobs), formatting passes, and all 319 release tests pass.
The two new differential tests compare with vector encoding across empty,
subtree-boundary, pending-replacement/extension, and prefixed-output cases,
before and after applying updates. All 19 new public lemmas were audited and
use only `propext`, `Classical.choice`, and `Quot.sound`; none inherits admissions,
native-evaluation axioms, or the Arc pointer axiom. All new modules are included
through `Tree.lean`. The retained Rust changes preserve streaming order and
allocation: explicit iterator loops replace adapters, and identical SSZ defaults
are written explicitly to avoid recursive trait dictionaries. External models
are concrete definitions over the pinned encoder's complete state, with no
replacement model of a milhouse method or Aeneas source change. The full goal
remains incomplete: decoding, serialization/deserialization, CoW stepping and
materializing mutation, Debug, semantic hashing/cache invariants, and
feature-specific APIs remain required.

Previous equality checkpoint (through `f986ee9`): the full Lean build passes
(1,842 jobs), all 317 release tests pass, and formatting passes. All 23 public
lemmas added since the preceding draft checkpoint were audited: eleven use
only standard Lean axioms, and twelve additionally use the existing trusted
`triomphe.arc.Arc.ptr_eq_spec`. None inherits an admission or native-evaluation
axiom. Every new module is included through `Tree.lean`. Equality proofs cover
the actual generated methods and preserve pointer shortcuts; sequence
soundness assumes only sound successful comparisons, not total comparisons.
The preceding extraction/model corrections (`2d2ca69`, `89044cc`) were validated
with fresh extraction, the full build, regression tests for nonreflexive shared
values and cache-insensitive equality, and the updated rebase axiom audits.
This proof checkpoint adds no Rust or Aeneas source changes. The full goal
remains incomplete: CoW stepping/dereferencing/materializing mutation, `Debug`,
codecs, semantic hashing/cache invariants, and feature-specific APIs remain
required.

Previous iterator-bridge and CoW-constructor checkpoint (through `99f4cbb`):
fresh extraction and the full Lean build pass (1,830 jobs). All 12 new public
lemmas and the updated `to_vec_spec` were audited and use only `propext`,
`Classical.choice`, and `Quot.sound`. Formatting and all 315 release tests pass.
The sole retained Rust change routes `to_vec` through its existing borrowed
`IntoIterator` implementation, whose body delegates directly to `iter`.
The new constructors, trait bridge, and proofs are included through `Tree.lean`.
No admissions, new axioms, opaque milhouse-method models, or Aeneas source
changes were introduced. CoW stepping still fails translation after both a
closure-free call and a small helper trial; those trial rewrites were removed
and the limitation is recorded as UPSTREAM_BUGS issue 16. The full goal remains
incomplete: CoW stepping/dereferencing/materializing mutation, remaining traits,
codecs, semantic hashing/cache invariants, and feature-specific APIs remain
required.

Previous rebase correctness checkpoint (through `54f84fa`): the full Lean build
passes (1,827 jobs), with all new modules included through `Tree.lean`. All six
progressive/list backing results and nine action/equality/content results were
audited. Five use only standard Lean axioms; ten operational results also use
the existing trusted `triomphe.arc.Arc.ptr_eq_spec` model law. No admissions or
new axioms were introduced. Rust, generated extraction, and Aeneas are unchanged
since the preceding extraction checkpoint. A fresh fetch also confirms that
`origin/main` at `d67aabd` remains included through merge `473f5c8`.
Rebase preserves backing validity without semantic equality/hash laws; its
contents specifications state the necessary positive-equality and cache laws
explicitly. The full goal remains incomplete: CoW iteration/materializing
mutation, remaining trait bridges, codecs, semantic hashing and cache-invariant
proofs, and feature-specific APIs remain in scope.

Previous cloning and binary-rebase checkpoint (through `091ede4`): fresh
extraction and the full Lean build pass (1,819 jobs), with every new module
included through `Tree.lean`. All 20 new or newly exposed results were audited.
The five clone results, seven pure/step foundations, and six list rebase-state
results use only standard Lean axioms; the two operational binary rebase
length/density results also use the existing trusted `triomphe.arc.Arc.ptr_eq_spec`
model law. No admissions or new axioms were introduced. Rust and Aeneas are
unchanged; the extraction script now includes the actual progressive rebase
operations and emits the derived list clone. Full rebase contents and
progressive backing preservation, CoW operations, remaining trait bridges,
codecs, hashing, and feature-specific APIs remain in scope.

Previous apply-updates backing-invariant checkpoint (through `c286169`): the full
Lean build passes (1,814 jobs). All 16 new or newly exposed window, range,
binary/progressive density, and list-level results were audited and use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets). The existing public
`iter` and `to_vec` specifications were audited again with the same result.
All new modules are included through `Tree.lean`. This checkpoint changes only
Lean proofs and imports; Rust, generated extraction, and Aeneas are unchanged.
The full goal remains incomplete: CoW iteration and materializing mutation,
trait bridges, rebase and its backing preservation, and remaining
codecs/hash/features still require work.

Previous front-removal and backing-invariant checkpoint: fresh extraction and the
full Lean build pass (1,810 jobs). All 14 new backing/streaming/front-removal
lemmas, plus the existing public `iter` and `to_vec` specifications after
regeneration, were audited and use only `propext`, `Classical.choice`, and
`Quot.sound`. Formatting and all 315 release tests pass. `pop_front` now uses a
concrete streaming builder helper to avoid documented upstream adapter,
early-return, and trait-dictionary limitations; its allocation strategy, clone
order, and error restoration are preserved, and Aeneas remains unchanged.
The later apply-updates checkpoint above extends backing-invariant preservation
to `apply_updates`; the other outstanding API obligations remain in scope.

Latest public-iteration and collection checkpoint: the full Lean build passes
(1,806 jobs), including all progressive traversal, public list iteration,
exact-size observers, and `to_vec` modules through `Tree.lean`. All 33 audited
binary/progressive/list traversal and collection results use only `propext`,
`Classical.choice`, and `Quot.sound` (or subsets). No Rust or Aeneas changes were
needed. This completes the sequence-level method proofs under their stated
representation invariants; it does not complete the full API goal. The
`IntoIterator` bridge, CoW iteration/materializing mutation, `pop_front`, rebase,
remaining traits/codecs/hash/features, and the complete mutation-preservation
audit for dense/representable backing layers remain outstanding.

Latest binary-iteration checkpoint: the full Lean build passes (1,792 jobs),
with the entire binary iterator development included through `Tree.lean`. All
eight new packed-step, node-descent, live-next, and suffix-enumeration results
were audited and use only `propext`, `Classical.choice`, and `Quot.sound` (or
subsets). This checkpoint changes only Lean proofs and their imports; Rust and
Aeneas are unchanged. The complete binary traversal result is a foundation for
the outstanding progressive-spine and pending-update iterator proofs, not a
claim that the public ProgressiveList iteration rows are complete.

Latest iterator-foundation checkpoint (through `0d85178`): the full Lean
build passes (1,788 jobs), with all new modules included through `Tree.lean`.
All 23 added or newly exposed constructor-trait, stack, path, construction,
trailing-zero, and leaf-step results were audited: their only axioms are
`propext`, `Classical.choice`, and `Quot.sound` (or subsets). The generated
`toStr` defaults initially introduced a native-evaluation size-check dependency;
the extraction script now supplies explicit kernel-checked size proofs, and the
renewed iterator audit has no native-evaluation dependency. Fresh extraction
succeeds without admissions. The committed Rust traversal refactors passed
formatting and all 315 release tests in the preceding verification; subsequent
changes affect only Lean proofs and extraction proof arguments. Aeneas remains
unchanged. Complete iterator enumeration and the remaining API rows above are
still outstanding.

Latest indexed-constructor checkpoint (through `cd982c5`): the full Lean build
passes (1,780 jobs), with all new modules included through `Tree.lean`. All 19
newly added or exposed results audited at this checkpoint use only `propext`,
`Classical.choice`, and `Quot.sound`. The successful `new` and `try_from_iter`
specifications now establish full sequence representation, including every
machine-indexed read, exact logical length, `SpineValid`, and no pending updates.
Builder validity and machine routing bounds are established internally. No Rust
or Aeneas sources changed at this checkpoint. The trait constructor wrappers,
public iteration APIs, and all other pending rows remain in the full objective.

Earlier progressive-construction checkpoint (through `63260ec`, with density
foundations in `b15cc65` and `088615d`): the full Lean build
passes (1,774 jobs), including every new module through `Tree.lean`. All 22
public results added in this checkpoint use only `propext`, `Classical.choice`,
and `Quot.sound`. Regenerated extraction contains no admissions. The equivalent
Rust iterator-helper refactor passes formatting, all 312 unit tests and three
integration tests in release mode. No changes were made to Aeneas. Exact
constructor sequence/length preservation is proved; builder geometry,
constructor indexed representation, trait constructor wrappers, and all other
pending API rows remain part of the full objective.

Latest binary-builder checkpoint (through `205ac24`): the full Lean build
passes (1,766 jobs). All 21 public loop and builder-content theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`. The two combined
finalization theorems initially exposed inherited `native_decide` dependencies
in older builder arithmetic; six checks were replaced with ordinary Lean
proofs covering both 32-bit and 64-bit platforms. No Rust or extracted-function
changes were needed. Progressive builder construction, iteration, and the
other pending API coverage remain part of the full objective.

Copy-on-write checkpoint (read/release proofs in `55e9e18`, plus the
metadata helpers): regenerated extraction and the full Lean build pass (1,760
jobs). All 13 public list read/release and metadata theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The equivalent Rust metadata
updates pass all 312 unit tests and three integration tests in release mode;
formatting passes. Rust handle dereferencing/materialization bridges and all
other pending operation coverage remain outstanding.

Previous checkpoint (through `e3a0107`, `9e7c79c`, with the recursive and list-level
modules included in `Tree.lean`): the full Lean build passes (1,756 jobs). All 36
audited public theorems in the geometry, shape, map-domain, progressive
bulk-update, list `apply_updates` contents, and list spine modules depend only
on `propext`, `Classical.choice`, and `Quot.sound`. Recursive progressive
bulk-update correctness and list `apply_updates` sequence preservation are now
proved. The other pending API coverage above remains part of the full goal.

The capacity/depth/layer checkpoint through `d64a58a` passed 1,749 build jobs
and audited 26 public theorems with the same standard-axiom-only result.

Earlier checkpoint (`9055d8d`, `10b5743`): the full Lean build passes (1,745 jobs),
including existing rebase and builder proofs after arithmetic sharing. All 71
audited public theorems across the new list/map, packed-leaf, binary bulk-update,
shape, and shared arithmetic modules depend only on `propext`,
`Classical.choice`, and `Quot.sound`. This does not complete the operation
coverage obligations above.

## Rust corrections

- `63321b0`: public `PackedLeaf::push` previously appended a value while
  retaining the old cached root. Hashing `[1u64]`, pushing `2`, and hashing
  again returned the packed bytes for `[1]`. A successful append now clears
  the cache with `get_mut`, requiring no lock acquisition; a full-leaf error
  still leaves both values and cache unchanged. Two regression tests and
  regenerated Lean state/content proofs cover this behavior. This minimal
  correction is needed for cache-validity proofs without an artificial
  assumption that callers only push to unhashed leaves.
- `0352f19`: `ProgressiveListIterCow::next_cow` advances its cursor only when
  yielding a handle. Exhaustion no longer increments indefinitely and eventually
  overflows. A regression test exercises the `usize::MAX` exhausted cursor in
  release mode; the Lean iterator correctness proof remains outstanding.
