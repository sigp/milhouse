# ProgressiveList proof coverage

The goal is correctness of every public `ProgressiveList` operation, including
the iterators and trait implementations exposed by that API. Extraction or a
wrapper equation alone does not establish an operation's full correctness.
Unchecked internal helpers are proof dependencies, not substitutes for the
public-operation specifications below.

Proofs use the extracted Rust definitions. Assumptions about generic update
maps, element cloning/equality, codecs, and hashing must state the laws actually
needed by the operation. Representation invariants must be established by
constructors and preserved by mutations; do not assume the postcondition in a
lower-level hypothesis and count the wrapper as proved.

## Coverage

| Operation | Required behavior | Current evidence / remaining work |
| --- | --- | --- |
| `empty`, `Default::default` | Empty contents, zero length, no pending updates | `Observers.lean` and `Contents.lean`: exact state, observer results, and representation of the empty sequence proved under the relevant empty-map laws; `Spine.lean` establishes the backing-spine invariant on successful construction without additional map laws |
| `new`, `try_from_iter`, `TryFrom<Vec<T>>`, `TryFromIter` | Preserve the input sequence and its length; establish representation invariants | `Construction/Total.lean`: all four actual public constructors/conversions now have total specifications, preserving every indexed value and logical length, establishing `BackingValid` and `SpineValid`, and leaving no pending updates. `ProgressiveTree/Builder/ExtendSuccess.lean` and `ProgressiveTree/ConstructionTotal.lean` prove iterator consumption, every insertion/rollover, and finalization succeed from packing layout and representability of occupied final layers. `Construction/Capacity.lean` proves this final `LengthFits` condition is necessary and sufficient for constructor success, given a finite input iterator and successful default map. Indexed representation adds only the relevant empty-map laws; vector input needs no iterator premise. No constructor, builder, or intermediate-loop success is assumed. Earlier `Representation.lean` and `Traits.lean` retain their successful-execution specifications |
| `len` | Length of the merged backing/pending view | `ProgressiveList/Length.lean` and `UpdateMap/Length.lean`: exact empty/nonempty-map arithmetic, backing lower bound, and successful evaluation below overflow proved; sequence agreement is established by constructor/mutation representation lemmas |
| `is_empty` | Equivalent to merged length zero | `ProgressiveList.is_empty_spec` proved |
| `has_pending_updates` | Equivalent to a nonempty update map | `ProgressiveList.has_pending_updates_spec` proved |
| `get` | Merged sequence indexing, with pending values taking precedence; out-of-bounds returns none | `Tree/ProgressiveList.lean`: precedence and backing correspondence; `Construction/Representation.lean` connects dense bounded backing trees to sequence representation, including out-of-bounds reads. Representation is now established by successful `new`/`try_from_iter`, as well as empty/default, and preserved by the proved mutations under their respective map laws |
| `push` | Append one value, increase length by one, preserve earlier values; reject full lists unchanged | `Push.lean` and `Contents.lean`: read-back, all-index preservation, exact length growth, success/full rejection, and `push_represents_append` proved; `Spine.lean` and `Backing.lean` preserve both backing-spine and dense/representable traversal invariants on success without extra map laws or capacity assumptions |
| `get_mut` | Read the current value; write-back changes only the chosen element; bounds and failure behavior | `Mutable.lean`: exact read/failure correspondence with `get`, successful handle construction, replacement of exactly one sequence element with unchanged length, and out-of-bounds no-op proved under the relevant generic map laws; clone identity is required only for read-value agreement, not replacement or missing reads; `Spine.lean` and `Backing.lean` preserve the backing-spine and full traversal invariants for every write-back |
| `get_cow` | Read without materializing an update; mutation writes only the chosen element and maintains map metadata | `CopyOnWrite.lean`: exact handle-data read/failure correspondence with `get`, successful access at every represented index, missing-handle behavior, and exact list restoration on unchanged release proved under generic map lookup/release laws, without a clone law; every write-back preserves the backing-spine and dense/representable traversal invariants. Rust `Deref` and materializing mutation bridges remain pending Aeneas translation limitations; handle-data observation is not a proof of those methods |
| `apply_updates` | Preserve merged contents and length; clear pending updates on success; restore state on error | `ApplyUpdates/Total.lean`: the actual public operation now has a total specification preserving the complete represented sequence and `BackingValid` and clearing pending updates. All rebuilding laws and final-capacity bounds are conditional on the nonempty branch. Input representation supplies lookup termination, the complete dense update domain, and a bound on the actual maximum. `ApplyUpdates/Capacity.lean` proves that, given coherent range/maximum metadata and terminating external calls, nonempty application succeeds if and only if the occupied final layers satisfy `LengthFits`; no unused-successor bound is assumed. Packed, binary, and progressive bulk-update totality establish every actual helper call. Earlier `ApplyUpdates.lean`, `Contents.lean`, and `Backing.lean` retain unconditional empty no-op, error restoration, successful-state/length facts, content/backing preservation, and idempotence |
| `iter`, `iter_from`, `IntoIterator` | Enumerate the merged sequence/suffix; reject invalid starting indices | `Iter/Construction.lean`: public `iter` enumerates the complete represented merged sequence; `iter_from` enumerates the requested suffix, accepts the end, and rejects oversized indices with the exact bounds error. Premises are representation, packing layout, and dense backing layers with representable capacities; no additional map-read, iterator-output, or termination assumptions. Binary and progressive traversal and the pending overlay are proved underneath. `Iter/Traits.lean` proves the same complete enumeration through the actual borrowed `IntoIterator` method, made reachable by `to_vec` |
| `ProgressiveListIter::next`, `size_hint`, `ExactSizeIterator::len` | Yield the next merged element; exact remaining length; exhaustion | `Iter/Next.lean`: live calls return the represented indexed value and preserve the constructed cursor; exhausted calls return unchanged `none`, including past-end indices. Pending replacements and extensions are covered. `Iter/Length.lean`: both size-hint bounds and exact length equal the represented suffix length; these observers require only agreement of the recorded and sequence lengths |
| `iter_cow`, `iter_cow_from`, `ProgressiveListIterCow::next_cow` | Enumerate mutable handles at successive indices; read-only and write-back behavior; exhaustion | `IterCow/Construction.lean`: the extracted constructors establish the exact backing suffix and merged pending overlay, retain the requested start and pending state, accept the logical end, and reject oversized starts with exact bounds errors and complete restoration. Premises are representation, backing validity, and packing layout, with no additional map or cloning laws. `IterCow/State.lean` proves exact unchanged release, error restoration, and backing preservation through arbitrary constructor continuations without representation or map-law premises. `next_cow` extraction/enumeration and handle dereferencing/materializing mutation remain pending borrowing limitations (UPSTREAM_BUGS issues 9 and 16); constructor invariants do not substitute for those proofs |
| `to_vec` | Return the merged sequence in order | `ToVec.lean`: actual collection succeeds and returns exactly the represented merged sequence. Uses the proved public iterator and exact-length results, representation, backing density/representability, packing layout, and successful identity cloning only for values in the sequence. Vector-push bounds and loop termination are derived internally |
| `pop_front` | Drop the specified prefix, reindex remaining values; reject oversized drops unchanged | `PopFront/Total.lean`: every in-bounds removal succeeds, represents exactly `contents.drop n`, and preserves `BackingValid`. Nonzero removal clears pending updates and requires successful identity cloning only for retained values, occupied capacity only for the retained suffix, and empty-default-map laws. These clone/capacity/map premises are conditional on nonzero removal; zero remains an unconditional no-op. `PopFront/BuilderTotal.lean` establishes actual streaming reconstruction success and the complete builder invariant. `PopFront/State.lean` proves oversized removals return the exact bounds error unchanged and every returned Rust error restores the original list. `Contents.lean` retains successful-execution content and backing proofs. No intermediate vector, assumed iterator output, successful-subcall premise, or opaque milhouse-method model |
| `rebase`, `rebase_on` | Preserve values, length, and pending updates while changing sharing only | `Rebase/Contents.lean`: both successful operations preserve the represented merged sequence and `BackingValid`, under input representation/backing validity, an accurately sized dense base, packing layout, soundness of true element `eq` and false element `ne`, and agreement of corresponding nonzero cached hashes at equal materialized lengths. Actual binary/progressive rebase content preservation is proved underneath, including shorter or longer bases. In-place rebase preserves exact pending-map state; nonmutating rebase adds only clone read/max laws. `Rebase/Backing.lean` proves backing preservation without equality, hash, or clone laws. `Rebase/State.lean` proves restoration on every returned in-place error and unchanged metadata/observers on all returned results. Deriving cache agreement from the eventual semantic hash model and maintained cache invariant remains part of the hashing work |
| `Clone` | Preserve logical contents and backing validity | `Clone.lean`: the actual derived clone shares the backing tree and copies its recorded length; successful cloning preserves `BackingValid` without clone laws. Sequence representation is preserved when pending-map cloning preserves reads and maximum; the pending observer is preserved under its corresponding map law. No element-clone law or exact identity of the cloned map is assumed |
| `PartialEq` | Characterize equality under element/map laws | `Equality/Correctness.lean`: actual extracted `eq` and `ne` terminate and characterize backing-tree structure, recorded length, and the explicit pending-map relation, under the element `ne` law and a law for the actual map pair only when preceding comparisons succeed. Hash caches are ignored. Positive equality transfers the represented sequence and `BackingValid` under only soundness of false element `ne` and pending-map read/max agreement; it assumes no comparison termination, completeness, reflexivity, packing layout, literal map identity, or representation/backing validity of the other list. Direct structural representation transfer needs no backing-validity premise. Binary/progressive recursive equality, pointer shortcuts, and structural invariant transport are proved underneath. This is structural equality, so identical merged contents alone do not imply a true comparison |
| `Debug` | Formatting through the derived formatter | Pending extraction and specification |
| `TreeHash` methods | Progressive merkleization with length mix-in; reject pending updates and unsupported packed operations | Pending hash model/extraction; existing binary-tree hash extraction limitations remain |
| `Encode` methods | SSZ encoding/encoded length of the merged sequence | `Encode/Length.lean`: exact fixed-width multiplication and variable payload-size sum plus four-byte offsets, with intermediate arithmetic bounds derived from the final byte bound. Fixed-size calculation needs no backing or traversal assumptions. `Encode/Fixed.lean`, `VariableLoop.lean`, and `Variable.lean`: actual `ssz_append` preserves the destination prefix and writes the exact represented merged payload, with the complete offset table for variable elements. `Encode/Owning.lean` proves both exact `as_ssz_bytes` formats. `Encode/Metadata.lean` proves variable-list classification, four-byte fixed-section width, and the concrete owning wrapper. Premises are representation, relevant traversal invariants/layout only for methods that iterate, element codec laws on the consumed values, final output-size bounds, and 32-bit bounds only on offsets actually emitted. No clone law or assumed iterator output is needed. `Tree/Ssz` models and proves the pinned external encoder state, offset writes, payload accumulation, and finalization |
| `Decode` methods | Decode SSZ contents, including empty/invalid/zero-sized-element cases | `Decode/FixedTotal.lean` and `VariableTotal.lean` prove successful public decoding of canonical bytes, exact indexed reads, recorded length, valid backing, and no pending updates, including empty lists and empty variable payloads. `FixedRoundtrip.lean` and `VariableRoundtrip.lean` compose actual owning encoding and public decoding, preserving the merged sequence and every indexed read while clearing pending updates. `Decode/Success.lean` proves streaming construction terminates with the exact decoded prefix and retained error. `ProgressiveTree/LengthFits.lean` and `Builder/PushLength.lean` derive every rollover bound from representability of the final sequence; fixed decoding retains this condition for general element widths, while the variable offset table supplies it internally. `Backing.lean` proves backing validity after any successful public decode without element-codec or parser laws. The cursor modules derive parsing from canonical bytes, including 32-bit bounds only on emitted offsets. `Decode/Entry.lean` covers metadata, empty input, zero fixed width, and short variable prefixes; `Ssz/VariableInit.lean` covers first-offset bounds/alignment/zero errors in the actual check order. `Decode/ErrorMessages.lean` proves exact builder-error text; `Ssz/ReadOffset.lean` proves four-byte reads and canonical offset roundtrips. Streaming bodies extract with the real error enum and local external models (UPSTREAM_BUGS issue 19); differential release tests cover error order and partial-builder finalization. `Decode/InitialErrors.lean` derives public first-offset bounds, alignment, and zero errors from raw offset bytes without packing, map, or element laws. `Decode/FixedErrors.lean` returns the first invalid element error after an arbitrary successful prefix, covering short final chunks and unconstrained bytes after a full-width invalid element. `Decode/VariableErrors.lean` derives second-offset fixed-section/bounds errors and third-offset decreasing errors directly from bytes, with exact element/error order. `Decode/ErrorResult.lean` propagates arbitrary cursor error traces through actual successful prefix finalization; `Ssz/DecodedLength.lean` derives variable prefix capacity from the table even for malformed input. `Ssz/VariablePrefix.lean`, `VariablePrefixErrors.lean`, and `VariableElementErrors.lean` derive every prefix step from raw table and payload bytes. `Decode/VariablePrefixErrors.lean` and `VariableElementErrors.lean` return the exact malformed-offset or element error after any successful prefix, including empty final payloads. `Decode/PayloadErrors.lean` generalizes both formats to per-entry payload bytes: equal values may have distinct accepted encodings, with no canonical-encoding assumption. `Ssz/PayloadTrace.lean` erases proof-level byte annotations to recover the exact original decoder trace. All public prefix-error results establish actual parser and builder behavior internally; later bytes and decoder calls are unconstrained |
| `Serialize`, `Deserialize` | Serialize merged sequence; reconstruct the deserialized sequence | Pending. A fresh concrete `Serialize` extraction probe reaches the actual `collect_seq` call but generates mutually recursive Serde dictionaries that fail Lean elaboration (UPSTREAM_BUGS issue 20). A faithful external protocol model or backend support must preserve serializer overrides, element behavior, errors, and iterator length hints. Excluding generic dispatch did not remove the cycle; no failed generated files, erased element dictionary, or opaque milhouse method is retained. Deserialization needs its own extraction/protocol work |
| Context deserialization feature | Reconstruct the contextual element sequence | Pending feature-specific extraction and proof |
| `Arbitrary` feature | Successful generation establishes a valid backing tree and length | Actual generator and four trait entry points now extract with the feature enabled. `Arbitrary/Models.lean` models the pinned external Vec control-byte loop and trait defaults, preserving consumed input, first errors, and input replacement by custom generators. High-level generator correctness proofs remain pending |

## Existing foundations

- `Tree/PackedLeaf/Insert.lean` proves necessary and sufficient position and
  vector bounds for insertion. `PackedLeaf/BulkUpdateSuccess.lean` proves
  actual vector cloning and the dense window scan terminate with the exact
  target length and merged indexed contents. Clone identity is scoped to
  copied stored and pending values; success and length need only terminating
  clones. The original global-clone content interfaces remain specializations.
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
  and contains no rebase call or result. Deriving it from semantic hashing and
  maintained cache validity remains a separate hashing obligation.
- `Tree/ProgressiveTree/Rebase/Steps.lean`, `Geometry.lean`, `Density.lean`,
  and `Contents.lean`: actual successful recursive calls either retain the
  original tree or rebuild from the binary action and recursive suffix. The
  calculated layer lengths match the dense materialized prefixes. Progressive
  rebasing preserves density and representable capacities with no equality,
  hash, or clone laws; only the original tree needs capacity bounds. Exact
  contents preservation adds true-`eq` and false-`ne` soundness and cache agreement
  for compared binary layers; unused progressive-node hashes need no law.
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
- `Tree/Arc/Equality.lean`, `Tree/Equality/Comparisons.lean`: faithful Arc
  comparison shortcuts and vector inequality foundations. The local external
  Arc model preserves the pinned triomphe implementation's pointer check, and
  `milhouse_models.vec_eq` negates the existing vector `ne` model to match Rust
  without an unstated element `eq`/`ne` coherence law. These corrections and
  extraction workarounds are recorded in UPSTREAM_BUGS issues 5, 12, and 17.
- `Tree/Equality/{Structure,Correctness,Soundness,Lookup}.lean` and
  `Tree/ProgressiveTree/Equality/{Structure,Correctness,Soundness,Lookup}.lean`:
  structure ignores hash caches but retains variants, zero depths, and values.
  Structural equality preserves materialized contents, density, and progressive
  capacity bounds. Actual recursive comparisons terminate and characterize
  this relation under the element `ne` law; positive-result soundness needs
  only the false-`ne` implication, without totality or completeness. No packing,
  density, cloning, or hash-content law is required by comparison correctness.
  Structural equality also preserves the complete extracted lookup computation,
  including errors and divergence, without layout, density, or bounds laws.
- `Tree/ProgressiveList/Equality/{Structure,Correctness}.lean`: list equality
  combines the proved progressive comparison, exact recorded length, and an
  explicit map relation that permits different internal cache states. The
  unconditional positive-result characterization derives the three actual
  successful comparisons. `partial_eq_represents` transfers represented
  contents and backing validity under only successful-comparison soundness
  and map read/max agreement; the other backing invariant is derived. Direct
  backing and merged lookup congruence remove the layout premise from this
  result, and pure representation transfer needs no backing invariant. The
  total `partial_eq_spec` and `partial_ne_spec` require the map law only for
  the actual pair when tree structure and recorded length agree.
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
  `Tree/ProgressiveList/ToVec.lean` derives successful exact vector collection
  through that trait bridge.
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

For each completed piece: build its Lean module, check the assumptions, and
commit with signing disabled and a model co-author trailer. Before completion:
regenerate the full extraction, build all proof modules, inspect axiom
dependencies for admissions, run the relevant Rust tests and formatting checks,
and audit every row above against concrete theorem statements.

Latest apply-updates totality checkpoint (through `79534c8`): the full Lean
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

- `0352f19`: `ProgressiveListIterCow::next_cow` advances its cursor only when
  yielding a handle. Exhaustion no longer increments indefinitely and eventually
  overflows. A regression test exercises the `usize::MAX` exhausted cursor in
  release mode; the Lean iterator correctness proof remains outstanding.
