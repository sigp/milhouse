# ProgressiveList proof coverage

## Goal and scope

Prove high-level correctness lemmas for every public `ProgressiveList`
operation within the scope below, including its iterators and trait
implementations. Build on the existing `Tree`, `ProgressiveTree`, and
`ProgressiveList` lemmas, organize them in separate files as appropriate, and
commit each completed piece. Proven lemmas must be free of extraneous
assumptions. If program semantics are counterintuitive or buggy, apply sensible,
minimal Rust changes that preserve intent and performance where possible.
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
| `new`, `try_from_iter`, `TryFrom<Vec<T>>`, `TryFromIter` | Preserve the input sequence and its length; establish representation invariants | `Construction/Trace.lean` derives the actual finite input sequence, exact length, and actual default map from successful construction without iterator, packing, or map-law assumptions; its indexed specification adds packing and empty-default-map laws. `Construction/Conditions.lean` proves success of all four entry points is equivalent to finite input (derived for vectors), occupied-layer capacity, and default-map success, without presupposing iterator termination or default construction. `Construction/Total.lean`: all four actual public constructors/conversions now have total specifications, preserving every indexed value and logical length, establishing `BackingValid` and `SpineValid`, and leaving no pending updates. `ProgressiveTree/Builder/ExtendSuccess.lean` and `ProgressiveTree/ConstructionTotal.lean` prove iterator consumption, every insertion/rollover, and finalization succeed from packing layout and representability of occupied final layers. `Construction/Capacity.lean` proves this final `LengthFits` condition is necessary and sufficient for constructor success, given a finite input iterator and successful default map. Indexed representation adds only the relevant empty-map laws; vector input needs no iterator premise. No constructor, builder, or intermediate-loop success is assumed. Earlier `Representation.lean` and `Traits.lean` retain their successful-execution specifications. `Construction/Caches.lean` proves every successful constructor initializes cleared caches without element, packing, map, or iterator laws. `CacheTotal.lean` adds validity relative to any mathematical reference hash to all four total specifications without additional premises. |
| `len` | Length of the merged backing/pending view | `ProgressiveList/Length.lean` and `UpdateMap/Length.lean`: exact empty/nonempty-map arithmetic, backing lower bound, and successful evaluation below overflow proved. `len_total_spec` and `len_success_iff` derive the complete public result directly from the actual optional map maximum and characterize success by representability of a present maximum's successor, without indexed-read or representation laws; sequence agreement is established by constructor/mutation representation lemmas |
| `is_empty` | Equivalent to merged length zero | `IsEmpty.lean`: exact total answer from optional maximum metadata, necessary-and-sufficient successor-bound success, and a premise-free true-result characterization by zero backing length and an actual absent maximum. No indexed-read, representation, packing, backing, or successful length-subcall premise. The map's separate emptiness method is not used. `Observers.lean` retains the logical-length comparison lemma |
| `has_pending_updates` | Equivalent to a nonempty update map | `ProgressiveList.has_pending_updates_spec` proved |
| `get` | Merged sequence indexing, with pending values taking precedence; out-of-bounds returns none | `Tree/ProgressiveList.lean`: precedence and backing correspondence; `Construction/Representation.lean` connects dense bounded backing trees to sequence representation, including out-of-bounds reads. Representation is now established by successful `new`/`try_from_iter`, as well as empty/default, and preserved by the proved mutations under their respective map laws |
| `push` | Append one value, increase length by one, preserve earlier values; reject full lists unchanged | `Push/Total.lean`: complete actual append execution is proved from represented contents and laws for only the insertion at the nonfull logical end. Success represents the exact appended sequence; full-list rejection preserves the entire input, and both branches preserve the exact backing fields. No push/length success, clone, packing, or structural invariant is assumed. `Push/Capacity.lean` characterizes success and full rejection from optional maximum metadata without indexed reads or representation; `Push/State.lean` proves every returned Rust error is exactly full-list rejection unchanged. Earlier `Push.lean` and `Contents.lean` retain read-back, all-index preservation, exact length growth, and successful-execution append results; `Spine.lean` and `Backing.lean` preserve both backing-spine and dense/representable traversal invariants on success without extra map laws or capacity assumptions. `ProgressiveList/Caches.lean` preserves every backing-cache predicate on all returned states, including full-list rejection, without additional laws. |
| `get_mut` | Return the pending value or actual clone of the backing value; write-back changes only the chosen element; bounds and failure behavior | `Mutable.lean`: exact pending-or-clone equation, including failures; read agreement with `get` needs clone identity only for the actual backing fallback. `Mutable/Total.lean`: `get_mut_total_spec` proves successful access at every machine index, exact initial-value behavior, single-element replacement with unchanged logical length and backing fields, and out-of-bounds no-op. Clone termination, write, and maximum-index laws are scoped to present elements; the missing-handle law is scoped to out-of-bounds access. No global clone law, clone identity, or structural backing premise is needed by the total replacement specification. `Spine.lean` and `Backing.lean` preserve the backing-spine and full traversal invariants for every write-back. `ProgressiveList/Caches.lean` preserves every backing-cache predicate through every returned mutable continuation without map or clone laws. |
| `get_cow` | Read without materializing an update; mutation writes only the chosen element and maintains map metadata | `CopyOnWrite.lean`: exact handle-data read/failure correspondence with `get`, successful access at every represented index, missing-handle behavior, and exact list restoration on unchanged release under generic map lookup/release laws, without cloning. `CopyOnWrite/Consuming.lean` proves actual `get_cow` followed by `Cow::into_mut` succeeds at every represented in-bounds index and every write replaces exactly that sequence element, preserving logical length and backing state. Premises are representation and the generic map's read, entry-location, occupied-handle, lookup-frame, and maximum laws; only a value absent from pending updates needs a terminating clone, and clone identity is unnecessary. `Cow/Consuming.lean` proves the actual consuming body, exact stored value/maximum write-back, and unchanged missing-entry rejection. Every list write-back also preserves backing-spine and dense/representable traversal invariants. Rust `Deref` and borrowed `make_mut` remain pending extraction limitations; neither handle-data observation nor consuming mutation substitutes for those methods. `ProgressiveList/Caches.lean` preserves every backing-cache predicate through arbitrary returned CoW handles, including consuming-mutation write-backs, without additional laws. |
| `apply_updates` | Preserve merged contents and length; clear pending updates on success; restore state on error | `ApplyUpdates/Total.lean`: the actual public operation now has a total specification preserving the complete represented sequence and `BackingValid` and clearing pending updates. All rebuilding laws and final-capacity bounds are conditional on the nonempty branch. Clone laws are scoped through the progressive and binary traversals to selected inputs for the actual maximum; no global element-clone law remains. Copied storage needs terminating clones, while identity is required only for retained stored slots and selected pending values; discarded stored copies need no identity law. Range-query termination and answer correctness are required only at reached progressive layers and selected binary queries for the actual maximum. Input representation supplies lookup termination, the complete dense update domain, and a bound on the actual maximum. `ApplyUpdates/Capacity.lean` proves that, given coherent range/maximum metadata and terminating external calls, nonempty application succeeds if and only if the occupied final layers satisfy `LengthFits`; no unused-successor bound is assumed. Packed, binary, and progressive bulk-update totality establish every actual helper call. `ApplyUpdates.lean`, `Contents.lean`, and `Backing.lean` retain unconditional empty no-op, error restoration, successful-state/length facts, content/backing preservation, and idempotence. Their successful-execution contracts also require rebuilding and default-map laws only on the actual nonempty branch; the state characterization records that branch answer. `ApplyUpdates/Caches.lean` proves cache-invariant preservation on every returned state, including Rust errors, without representation, shape, packing, map, clone, or termination laws. `CacheTotal.lean` adds validity relative to a mathematical reference hash to the complete total specification, requiring only the input cache invariant in addition to the existing total-operation premises |
| `iter`, `iter_from`, `IntoIterator` | Enumerate the merged sequence/suffix; reject invalid starting indices | `Iter/Construction.lean`: public `iter` enumerates the complete represented merged sequence; `iter_from` enumerates the requested suffix, accepts the end, and rejects oversized indices with the exact bounds error. Accepted-constructor premises are representation, packing layout, and dense backing layers with representable capacities; no additional map-read, iterator-output, or termination assumptions. `Iter/Bounds.lean` derives rejection from only actual optional maximum metadata and the oversized-index comparison, replacing its former representation premise; it also characterizes every returned bounds error. Binary and progressive traversal and the pending overlay are proved underneath. `Iter/Traits.lean` proves the same complete enumeration through the actual borrowed `IntoIterator` method, made reachable by `to_vec` |
| `ProgressiveListIter::next`, `size_hint`, `ExactSizeIterator::len` | Yield the next merged element; exact remaining length; exhaustion | `Iter/Next.lean`: live calls return the represented indexed value and preserve the constructed cursor; exhausted calls return unchanged `none`, including past-end indices. Pending replacements and extensions are covered. `Iter/Length.lean`: both size-hint bounds and exact length equal the represented suffix length; these observers require only agreement of the recorded and sequence lengths |
| `iter_cow`, `iter_cow_from`, `ProgressiveListIterCow::next_cow` | Enumerate mutable handles at successive indices; read-only and write-back behavior; exhaustion | `IterCow/Construction.lean`: the extracted constructors establish the exact backing suffix and merged pending overlay, retain the requested start and pending state, accept the logical end, and reject oversized starts with exact bounds errors and complete restoration. Accepted-constructor premises are representation, backing validity, and packing layout, with no additional map or cloning laws. `IterCow/Bounds.lean` proves exact agreement with read-only bounds errors and the constant original-state continuation. Its rejection theorem needs only optional maximum metadata and the numeric comparison, with no sequence reads, representation, backing, or packing premise. `IterCow/State.lean` proves exact unchanged release, error restoration, and backing preservation through arbitrary constructor continuations without representation or map-law premises. `next_cow` extraction/enumeration, handle dereferencing, and borrowed `make_mut` remain pending borrowing limitations (UPSTREAM_BUGS issues 9 and 16). Consuming handles through `into_mut` is proved separately; neither that result nor constructor invariants substitutes for iterator stepping. `ProgressiveList/Caches.lean` proves backing-cache preservation through every constructor continuation and returned error; this does not substitute for the still-unextracted iterator step. |
| `to_vec` | Return the cloned merged sequence in order | `ToVec/Loop.lean` and `Clones.lean`: actual collection equals ordered `List.mapM` of element cloning, including exact returned values, failures, and divergence, without clone laws. `Total.lean`: success is equivalent to successful termination of clones of represented values; the actual cloned output preserves length. Uses representation, backing density/representability, and packing layout; traversal and vector-push bounds are derived internally. `ToVec.lean` retains the original exact-contents contracts as specializations under identity cloning only for values in the sequence |
| `pop_front` | Drop the specified prefix and clone retained values in order; reject oversized drops unchanged | `PopFront/Clones.lean` proves successful nonzero removal stores exactly the ordered retained clone results, records their count, builds valid backing, and installs the actual default map, without clone laws or default-map semantics. `ClonesTotal.lean` proves the complete indexed sequence contract for those actual clone results from retained clone termination, occupied retained capacity, and the relevant empty-default-map laws; clone identity is unnecessary. `Contents.lean` and `Total.lean` derive the original unchanged-suffix contracts as identity-clone specializations, with rebuilding laws conditional on nonzero removal. `Conditions.lean` characterizes success for every count: zero, or an in-bounds removal with occupied retained capacity, successful retained clones, and a successful default map. Representation is needed only for nonzero calls; packing layout and backing validity only for reached rebuilds. `Capacity.lean` retains the earlier capacity-only specialization. `BuilderClones.lean` establishes actual cloned streaming contents and count; the original builder contents/count proofs reuse it. `BuilderTotal.lean` proves every streaming push succeeds and preserves the complete builder invariant. `State.lean` proves zero is an unconditional no-op, oversized removal returns the exact bounds error, and every returned Rust error restores the input. `Caches.lean` proves nonzero success rebuilds cleared caches and every returned state preserves any zero-accepting cache predicate. No intermediate vector, assumed iterator output, successful-subcall premise in total contracts, or opaque milhouse-method model. |
| `rebase`, `rebase_on` | Preserve values, length, and pending updates while changing sharing only | `Rebase/Total.lean`: both operations terminate successfully and preserve the represented merged sequence and `BackingValid`, under input representation/backing validity, an accurately sized dense base, packing layout, soundness of true element `eq` and false element `ne` only at corresponding reached leaves/pairs, terminating comparisons only on paths selected by the pointer/hash/length guards and through the first true packed element `ne`, and equal-length nonzero cache-shortcut soundness. Binary/progressive success is established from shape and original capacity invariants, with all arithmetic and recursive calls derived. In-place rebase preserves exact pending-map state and requires no map or element-clone law; nonmutating rebase requires only the actual pending-map clone to terminate and preserve reads/maximum, and returns exactly that cloned map. `Rebase/Backing.lean` proves backing preservation without equality, hash, or clone laws. `Rebase/State.lean` proves in-place error restoration and unchanged metadata/observers; nonmutating observer preservation needs only the corresponding clone maximum/emptiness laws. `Rebase/Caches.lean` adds successful-execution and total specifications preserving arbitrary cache predicates indexed by the stored values and binary/progressive depth. The actual recursion preserves original progressive caches and may import binary caches from the base; base progressive-cache validity is unnecessary. Backing-cache results require no pending-map clone semantics. `Rebase/Validity.lean` derives the operational cache-shortcut law from reference-valid input caches and collision soundness on finite corresponding binary input pairs, omitting original zero-cache nodes and all progressive caches. It provides successful-execution and total public specifications and validity on every returned in-place state. `Rebase/Cleared.lean` proves both total rebase variants from cleared original caches without any collision assumption. `Tree/Rebase/Soundness.lean` and `ProgressiveTree/Rebase/Soundness.lean` restrict equality laws to the actual pair of backing trees, omit element laws on pointer shortcuts and unequal-length packed vectors, and are used by every public rebase contents/cache specification. Pointer sharing now prunes all descendant comparison, equality, and collision obligations; eligible nonzero equal-hash/equal-length shortcuts also prune descendant comparison, equality, and collision laws. `Rebase/Pointer.lean` proves in-place rebasing onto shared backing returns the complete original list and nonmutating rebasing performs exactly the pending-map clone, without structural, packing, or semantic comparison assumptions. `Tree/Rebase/ComparisonInputs.lean` tracks supplied optional lengths and exact child splits; the binary/progressive success inductions and every public total contract use those metadata-specific scopes. `ElementComparisons.lean` proves both sufficiency and reflection for the external short-circuit loop, leaving pairs after the first true `ne` unconstrained. Packed false-`ne` soundness now uses the same short circuit through `NeOn`; duplicate vector soundness proofs are consolidated. Actual semantic reference hashing and shared cache writes remain pending |
| `Clone::clone` | Preserve logical contents and backing validity | `Clone/Total.lean` proves that actual list-clone success is equivalent to success of the pending-map clone, without representation, packing, or element laws. Its total specification preserves the represented sequence, valid backing, exact backing fields, and the actual cloned pending map under only termination and read/maximum preservation for that map call. No successful list-clone call is assumed. `Clone.lean`: the actual derived clone shares the backing tree and copies its recorded length; successful cloning preserves `BackingValid` without clone laws. Sequence representation is preserved when pending-map cloning preserves reads and maximum; the pending observer is preserved under its corresponding map law. No element-clone law or exact identity of the cloned map is assumed. `ProgressiveList/Caches.lean` preserves every backing-cache predicate without element or pending-map clone laws. |
| `Clone::clone_from` | Replace the destination with a clone of the source | `Clone/From.lean` connects the concrete Rust caller to the actual inherited trait default and characterizes its computation, including clone failure/divergence. Success is equivalent to success of the source pending-map clone. The total contract replaces the represented sequence, preserves source backing validity and exact backing fields, and returns the actual cloned source map. All map laws concern only that source clone; the destination requires no invariant. Successful replacement preserves source cache predicates without map semantics, and the pending observer transfers under only the corresponding emptiness law. It calls the source map's `clone`, so no map `clone_from` law is needed. The proof-only root and actual generated dictionary are retained; no production implementation or external model is substituted. |
| `PartialEq` | Characterize equality under input-scoped element/map laws | `Equality/Correctness.lean`: actual extracted `eq` and `ne` terminate and characterize backing-tree structure, recorded length, and the explicit pending-map relation. Element `ne` laws cover only selected input pairs, respecting pointer shortcuts, packed-vector length rejection, and field/element short circuiting; the map law applies only to the actual pair when preceding comparisons succeed. Hash caches are ignored. Positive equality transfers the represented sequence and `BackingValid` under only input-scoped false-`ne` soundness and pending-map read/max agreement; it assumes no comparison termination, completeness, reflexivity, packing layout, literal map identity, or representation/backing validity of the other list. Direct structural representation transfer needs no backing-validity premise. `Equality/Pointer.lean` gives the exact shared-backing computation without element or map laws, including map failure/divergence. This is structural equality, so identical merged contents alone do not imply a true comparison |
| `Debug` for the list and both iterator types | Out of scope | Explicitly excluded from the proof goal, including `ProgressiveList`, `ProgressiveListIter`, and `ProgressiveListIterCow`. Historical formatter and lock-model findings are retained in UPSTREAM_BUGS issue 5. These implementations are not claimed proved. |
| `TreeHash` methods | Deferred; out of scope for now | `TreeHash/Metadata.lean` retains the proofs of List classification and unconditional rejection of unsupported packing methods. Root computation, pending-update rejection through the public root, length mix-in, parallel hashing, and shared hash-cache writes are deferred under the revised goal. Aeneas limitations are recorded in UPSTREAM_BUGS issue 21; the root implementation is not claimed proved. |
| `Encode` methods | SSZ encoding/encoded length of the merged sequence | `Encode/FixedLength.lean` and `Encode/Length.lean`: exact fixed-width multiplication and variable payload-size sum plus four-byte offsets. The fixed-width numeric contract requires only logical length, and the total contract derives that length internally from the returned map maximum, without indexed reads or sequence representation. Its success criterion proves successor representability and the final byte bound are necessary and sufficient; the successor check remains necessary at zero width. Variable-size accumulation derives intermediate bounds from the final byte bound. Fixed-size calculation needs no backing or traversal assumptions. `Encode/Fixed.lean`, `VariableLoop.lean`, and `Variable.lean`: actual `ssz_append` preserves the destination prefix and writes the exact represented merged payload, with the complete offset table for variable elements. `Encode/Owning.lean` proves both exact `as_ssz_bytes` formats. `Encode/Metadata.lean` proves variable-list classification, four-byte fixed-section width, and the concrete owning wrapper. Representation and traversal invariants/layout are required only by methods that iterate. The remaining premises are the relevant element codec/size laws on consumed values, final output-size bounds, and 32-bit bounds only on offsets actually emitted. No clone law or assumed iterator output is needed. `Tree/Ssz` models and proves the pinned external encoder state, offset writes, payload accumulation, and finalization |
| `Decode` methods | Decode SSZ contents, including empty/invalid/zero-sized-element cases | `Decode/Trace.lean` and `PublicTrace.lean` derive the actual input-bound per-occurrence payload trace, stored values/count, and default map from any successful decode, with no supplied parser trace, canonical encoding, codec law, or packing premise. Indexed representation, backing validity, and no pending updates add only empty-default-map laws and packing layout for nonempty input. `Conditions.lean` proves public success is equivalent to a complete `SszItems.DecodesBytes` trace, occupied-layer capacity, and a successful default map; this criterion needs no map-content or codec law. `Decode/PayloadFixed.lean` and `PayloadVariable.lean` prove total public decoding from independently accepted payload occurrences, including different encodings of equal values, empty variable payloads, empty input, and an accepted short final fixed chunk. They establish exact indexed contents, valid backing, and no pending updates; metadata/layout/capacity laws are omitted on empty input. `Fixed.lean`, `FixedTotal.lean`, `Variable.lean`, and `VariableTotal.lean` provide canonical-byte contracts with metadata and packing premises conditional on nonempty contents; fixed positivity and capacity are conditional as well. Their sequence specifications share `from_ssz_bytes_represents`. `FixedRoundtrip.lean` and `VariableRoundtrip.lean` compose actual owning encoding and public decoding, preserving the merged sequence and every indexed read while clearing pending updates. `Decode/Success.lean` proves streaming construction terminates with the exact decoded prefix and retained error. `ProgressiveTree/LengthFits.lean` and `Builder/PushLength.lean` derive every rollover bound from representability of the final sequence; fixed decoding retains this condition for general element widths, while the variable offset table supplies it internally. `Backing.lean` proves backing validity after any successful public decode without element-codec or parser laws. The cursor modules derive parsing from canonical bytes, including 32-bit bounds only on emitted offsets. `Decode/Entry.lean` covers metadata, empty input, zero fixed width, and short variable prefixes; `Ssz/VariableInit.lean` covers first-offset bounds/alignment/zero errors in the actual check order. `Decode/ErrorMessages.lean` proves exact builder-error text; `Ssz/ReadOffset.lean` proves four-byte reads and canonical offset roundtrips. Streaming bodies extract with the real error enum and local external models (UPSTREAM_BUGS issue 19); differential release tests cover error order and partial-builder finalization. `Decode/InitialErrors.lean` derives public first-offset bounds, alignment, and zero errors from raw offset bytes without packing, map, or element laws. `Decode/FixedErrors.lean` returns the first invalid element error after an arbitrary successful prefix, covering short final chunks and unconstrained bytes after a full-width invalid element. `Decode/VariableErrors.lean` derives second-offset fixed-section/bounds errors and third-offset decreasing errors directly from bytes, with exact element/error order. `Decode/ErrorResult.lean` propagates arbitrary cursor error traces through actual successful prefix finalization; `Ssz/DecodedLength.lean` derives variable prefix capacity from the table even for malformed input. `Ssz/VariablePrefix.lean`, `VariablePrefixErrors.lean`, and `VariableElementErrors.lean` derive every prefix step from raw table and payload bytes. `Decode/VariablePrefixErrors.lean` and `VariableElementErrors.lean` return the exact malformed-offset or element error after any successful prefix, including empty final payloads. `Decode/PayloadErrors.lean` generalizes both formats to per-entry payload bytes: equal values may have distinct accepted encodings, with no canonical-encoding assumption. `Ssz/PayloadTrace.lean` erases proof-level byte annotations to recover the exact original decoder trace. All public prefix-error results establish actual parser and builder behavior internally; later bytes and decoder calls are unconstrained. `Decode/Caches.lean` proves every successful public decoder initializes cleared caches, also covering partial lists finalized after streaming element errors, without parser, packing, map, element, or finiteness laws. |
| `Serialize`, `Deserialize`, `Deserialize::deserialize_in_place` | Out of scope | Explicitly excluded from the proof goal, including the inherited in-place default and visitor/sequence protocols. Historical extraction and source-audit findings are retained in UPSTREAM_BUGS issues 20 and 22. These implementations are not claimed proved. |
| Context deserialization feature | Out of scope | Serde-based `ContextDeserialize` and its contextual visitor/seed protocol are explicitly excluded from the proof goal. Historical extraction findings are retained in UPSTREAM_BUGS issue 22. This implementation is not claimed proved. |
| `Arbitrary` feature | Successful generation establishes a valid backing tree and length | `Arbitrary/Behavior.lean` proves every successful actual generator stores the exact generated backing sequence and length and establishes `BackingValid`, without element-generation or default-map laws. `Generated.lean` derives the actual finite control/element trace from every successful call and proves indexed representation, valid backing/spine, and no pending updates under packing and empty-default-map laws. `Total.lean` proves actual generation and construction succeed along finite element traces; occupied-layer `LengthFits` is necessary and sufficient for success under a terminating default map. First element errors propagate unchanged with their consumed input and need no construction laws; constructor errors map to `IncorrectFormat`. `Traits.lean` proves both size-hint methods at every depth and the actual owning-input default, including its total representation and successful backing guarantees. The feature and all four trait entry points are extracted. `Tree/Arbitrary/Models.lean`, `Generation.lean`, and `Reflection.lean` model and prove pinned external Vec collection, including even stopping-byte consumption, first-error state, and custom input replacement; vector success is equivalent to a finite trace. No opaque milhouse method or assumed intermediate success. `Arbitrary/Caches.lean` proves both ordinary and owning-input generation initialize cleared caches on every successful result, without generator, packing, or map laws. |

## Existing foundations

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
  returned Rust errors.
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
- `Tree/ProgressiveList/Encode/Fixed.lean`, `VariableLoop.lean`, `Variable.lean`,
  `Owning.lean`, and `Metadata.lean`: exact SSZ bytes through all actual encoding
  methods, including pending replacements/extensions and nonempty destination
  prefixes. Variable encoding writes offsets relative to the beginning of the
  encoded list, followed by the payloads in iterator order. Encoder continuation
  composition and final borrowed-buffer release are proved. `as_ssz_bytes`
  delegates to the proved append body with an empty vector, without cloning or
  a separate length pass. Primitive element append laws preserve the supplied
  buffer prefix and are required only for represented values and fitting
  buffers; fixed elements additionally match their declared width.
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
- `Tree/ProgressiveList/Clone/From.lean`: the actual public trait default and
  extraction-only caller agree. The default performs the source list clone;
  success is exactly source pending-map clone success. Successful and total
  source-sequence replacement preserve source backing invariants and exact
  backing fields, with no old-destination condition. Source cache predicates
  and the pending observer transfer under their own relevant premises. The
  source map's `clone_from` is never invoked, and no element clone law is added.
- `Tree/ProgressiveList/Clone/Total.lean`: list-clone success is equivalent to
  pending-map clone success, without representation or generic element laws.
  A terminating map clone preserving reads and maximum gives actual list
  termination, complete sequence and backing validity, unchanged tree and
  recorded length, and exactly that cloned pending map. The total contract
  assumes no own-method success, map identity, element cloning, or packing law.
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
  laws; nonmutating rebasing adds only pending-map clone read/max preservation.
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
  clone's read/maximum laws. The additional `Rebase/State.lean` lemmas prove
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
- `Tree/Cow/Value.lean`, `Tree/UpdateMap/CopyOnWrite.lean`,
  `Tree/ProgressiveList/CopyOnWrite.lean`: observation of extracted handle data,
  the generic map's read/release laws, and read-only sequence correctness.
  Exact unchanged release preserves all list fields, including pending-map
  metadata; arbitrary write-back preserves the backing spine. No bridge from
  the data observer to Rust `Deref` or materializing mutation is assumed.
- `Tree/Cow/Metadata.lean`: the extracted callback records the exact maximum,
  clears its action, and executes only once; attaching maximum-index tracking
  changes no carried value and unchanged release restores the original handle
  and metadata. Equivalent direct Rust metadata updates avoid built-in
  `Option::take` and `Ord::max` model mismatches. Full handle-method limitations
  and the supported extraction boundary are documented in `UPSTREAM_BUGS.md`.
- `Tree/ProgressiveList/Mutable.lean` and `Mutable/Total.lean`: the exact
  pending-or-clone read equation preserves nonidentity clone results and
  failures. Present-element success needs termination of only the fallback
  clone that can actually be called. `get_mut_spec` composes that execution
  with exact sequence replacement and backing-field preservation;
  `get_mut_total_spec` covers every index, including missing-index restoration.
  Write/max laws apply only in bounds, and the missing-handle law only out of
  bounds. The older read-agreement lemmas now scope clone identity to the
  actual fallback instead of every value of the element type.
- `Tree/Cow/EntryModels.lean`, `EntrySuccess.lean`: external BTree/Vec vacant
  entries retain keyed exclusive-slot write-back state instead of `Unit`.
  Vector slots retain original backing length so the pinned growth calculation
  and vector-size checks are preserved. An index below the machine maximum
  supplies all arithmetic successes and the exact resulting backing length.
  Other keys and occupancy belong to the enclosing map continuation; allocation
  failure is abstracted as in the existing collection models.
- `Tree/Cow/Consuming.lean`: the actual consuming body succeeds from a located
  entry and clone termination only on its immutable branch. It returns the
  actual clone result, without assuming clone identity; mutable values are
  reused directly. `Written` records the exact entry and maximum-index effects
  of every replacement through the extracted continuation. Missing entries
  reject without cloning or changing maximum metadata. Concrete inline Rust
  helpers and explicit result matches avoid the borrowed trait/adapter
  limitations while preserving the public API and operation order.
- `Tree/UpdateMap/CowWriteBack.lean`,
  `Tree/ProgressiveList/CopyOnWrite/Consuming.lean`: generic entry-location,
  occupied-handle, lookup-frame, and maximum laws compose with actual `get_cow`
  and `into_mut` to prove complete in-bounds sequence replacement. Theorem
  `get_cow_into_mut_spec` derives the handle and every consuming subcall,
  preserves logical length and exact backing fields, and requires no packing
  or backing invariant beyond indexed list representation. Only absence from
  the pending map requires cloning the one queried value. `Deref`, borrowed
  `make_mut`, and CoW iterator stepping remain separate open obligations.
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

Latest packing-layout checkpoint (through `0932572`, with numeric foundation
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
