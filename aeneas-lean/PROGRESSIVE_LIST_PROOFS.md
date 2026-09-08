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
| `new`, `try_from_iter`, `TryFrom<Vec<T>>`, `TryFromIter` | Preserve the input sequence and its length; establish representation invariants | `Construction/Representation.lean`: successful `new` and `try_from_iter` represent the exact input sequence at every machine index (including out of bounds), have its exact logical length, establish `SpineValid`, and have no pending updates. The progressive builder invariant is established by construction and preserved through every push, rollover, and iterator step; finalization establishes density and representable layer capacities. Indexed-read bounds are derived internally. Premises are the relevant packing and empty-default-map laws, plus actual iterator output for generic input; vector input needs no iterator premise. `Construction/Traits.lean` lifts the same complete specification through the extracted `TryFrom<Vec<T>>` and SSZ `TryFromIter` wrappers |
| `len` | Length of the merged backing/pending view | `ProgressiveList/Length.lean` and `UpdateMap/Length.lean`: exact empty/nonempty-map arithmetic, backing lower bound, and successful evaluation below overflow proved; sequence agreement is established by constructor/mutation representation lemmas |
| `is_empty` | Equivalent to merged length zero | `ProgressiveList.is_empty_spec` proved |
| `has_pending_updates` | Equivalent to a nonempty update map | `ProgressiveList.has_pending_updates_spec` proved |
| `get` | Merged sequence indexing, with pending values taking precedence; out-of-bounds returns none | `Tree/ProgressiveList.lean`: precedence and backing correspondence; `Construction/Representation.lean` connects dense bounded backing trees to sequence representation, including out-of-bounds reads. Representation is now established by successful `new`/`try_from_iter`, as well as empty/default, and preserved by the proved mutations under their respective map laws |
| `push` | Append one value, increase length by one, preserve earlier values; reject full lists unchanged | `Push.lean` and `Contents.lean`: read-back, all-index preservation, exact length growth, success/full rejection, and `push_represents_append` proved; `Spine.lean` preserves the backing-spine invariant on success without extra map laws or capacity assumptions |
| `get_mut` | Read the current value; write-back changes only the chosen element; bounds and failure behavior | `Mutable.lean`: exact read/failure correspondence with `get`, successful handle construction, replacement of exactly one sequence element with unchanged length, and out-of-bounds no-op proved under the relevant generic map laws; clone identity is required only for read-value agreement, not replacement or missing reads; `Spine.lean` preserves the backing-spine invariant for every write-back |
| `get_cow` | Read without materializing an update; mutation writes only the chosen element and maintains map metadata | `CopyOnWrite.lean`: exact handle-data read/failure correspondence with `get`, successful access at every represented index, missing-handle behavior, and exact list restoration on unchanged release proved under generic map lookup/release laws, without a clone law; every write-back preserves the backing-spine invariant. Rust `Deref` and materializing mutation bridges remain pending Aeneas translation limitations; handle-data observation is not a proof of those methods |
| `apply_updates` | Preserve merged contents and length; clear pending updates on success; restore state on error | `ApplyUpdates.lean`: empty no-op, error restoration, successful state, logical-length preservation, cleared pending updates, and idempotence; `ApplyUpdates/Contents.lean`: `apply_updates_represents` preserves the sequence at every index and the backing-spine invariant, using the complete recursive progressive proof. Extension completeness is derived from the old representation. Premises are the input spine invariant and the relevant packing, clone, range, maximum-bound, and default-map laws |
| `iter`, `iter_from`, `IntoIterator` | Enumerate the merged sequence/suffix; reject invalid starting indices | `Iter/Construction.lean`: public `iter` enumerates the complete represented merged sequence; `iter_from` enumerates the requested suffix, accepts the end, and rejects oversized indices with the exact bounds error. Premises are representation, packing layout, and dense backing layers with representable capacities; no additional map-read, iterator-output, or termination assumptions. Binary and progressive traversal and the pending overlay are proved underneath. The `IntoIterator` trait bridge remains pending extraction |
| `ProgressiveListIter::next`, `size_hint`, `ExactSizeIterator::len` | Yield the next merged element; exact remaining length; exhaustion | `Iter/Next.lean`: live calls return the represented indexed value and preserve the constructed cursor; exhausted calls return unchanged `none`, including past-end indices. Pending replacements and extensions are covered. `Iter/Length.lean`: both size-hint bounds and exact length equal the represented suffix length; these observers require only agreement of the recorded and sequence lengths |
| `iter_cow`, `iter_cow_from`, `ProgressiveListIterCow::next_cow` | Enumerate mutable handles at successive indices; read-only and write-back behavior; exhaustion | Pending |
| `to_vec` | Return the merged sequence in order | `ToVec.lean`: actual collection succeeds and returns exactly the represented merged sequence. Uses the proved public iterator and exact-length results, representation, backing density/representability, packing layout, and successful identity cloning only for values in the sequence. Vector-push bounds and loop termination are derived internally |
| `pop_front` | Drop the specified prefix, reindex remaining values; reject oversized drops unchanged | Pending operation extraction and proof; construction and iteration foundations are now available |
| `rebase`, `rebase_on` | Preserve values, length, and pending updates while changing sharing only | Pending ProgressiveTree rebase content proof |
| `Clone`, `PartialEq` | Preserve logical contents on clone; characterize equality under element/map laws | Pending extraction and proof |
| `Debug` | Formatting through the derived formatter | Pending extraction and specification |
| `TreeHash` methods | Progressive merkleization with length mix-in; reject pending updates and unsupported packed operations | Pending hash model/extraction; existing binary-tree hash extraction limitations remain |
| `Encode` methods | SSZ encoding/encoded length of the merged sequence | Pending codec models and proofs |
| `Decode` methods | Decode SSZ contents, including empty/invalid/zero-sized-element cases | Pending codec models and proofs |
| `Serialize`, `Deserialize` | Serialize merged sequence; reconstruct the deserialized sequence | Pending serializer models and proofs |
| Context deserialization feature | Reconstruct the contextual element sequence | Pending feature-specific extraction and proof |
| `Arbitrary` feature | Successful generation establishes a valid backing tree and length | Pending feature-specific extraction and constructor proof |

## Existing foundations

- `Tree/Invariants.lean`, `Tree/Builder.lean`, `Tree/Roundtrip.lean`,
  `Tree/Rebase.lean`: binary-tree density, builder invariants, leaf-update
  read-back, and rebase shape preservation. Content preservation must be proved
  separately where the existing result establishes only density.
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
  return the remaining sequence length. `Tree/ProgressiveList/ToVec.lean`
  derives successful exact vector collection from that enumeration.
  These public results use dense, representable backing layers. Constructors
  supply these properties through builder finalization; completing their
  preservation across all mutating APIs, particularly backing rebuilds, remains
  part of the full goal alongside the previously proved representation and
  `SpineValid` preservation results.
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
  push, and mutable write-back. Binary density is a separate property for
  future operations that need more than these structural and sequence facts.
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
