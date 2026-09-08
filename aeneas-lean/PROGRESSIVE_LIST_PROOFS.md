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
| `empty`, `Default::default` | Empty contents, zero length, no pending updates | `Observers.lean` and `Contents.lean`: exact state, observer results, and representation of the empty sequence proved under the relevant empty-map laws; structural invariant still to be instantiated |
| `new`, `try_from_iter`, `TryFrom<Vec<T>>`, `TryFromIter` | Preserve the input sequence and its length; establish representation invariants | Pending progressive-builder extraction and content proofs |
| `len` | Length of the merged backing/pending view | `ProgressiveList/Length.lean` and `UpdateMap/Length.lean`: exact empty/nonempty-map arithmetic, backing lower bound, and successful evaluation below overflow proved; sequence agreement is established by constructor/mutation representation lemmas |
| `is_empty` | Equivalent to merged length zero | `ProgressiveList.is_empty_spec` proved |
| `has_pending_updates` | Equivalent to a nonempty update map | `ProgressiveList.has_pending_updates_spec` proved |
| `get` | Merged sequence indexing, with pending values taking precedence; out-of-bounds returns none | `Tree/ProgressiveList.lean`: precedence and backing correspondence proved; full representation theorem pending |
| `push` | Append one value, increase length by one, preserve earlier values; reject full lists unchanged | `Push.lean` and `Contents.lean`: read-back, all-index preservation, exact length growth, success/full rejection, and `push_represents_append` proved; structural tree/map invariant preservation remains for later bulk-update proofs |
| `get_mut` | Read the current value; write-back changes only the chosen element; bounds and failure behavior | `Mutable.lean`: exact read/failure correspondence with `get`, successful handle construction, replacement of exactly one sequence element with unchanged length, and out-of-bounds no-op proved under the relevant generic map laws; clone identity is required only for read-value agreement, not replacement or missing reads; structural invariant preservation remains |
| `get_cow` | Read without materializing an update; mutation writes only the chosen element and maintains map metadata | Extracted via the closure-free map helper with lazy backing lookup; semantic and write-back proofs pending |
| `apply_updates` | Preserve merged contents and length; clear pending updates on success; restore state on error | `ApplyUpdates.lean`: empty no-op, error restoration, successful state, logical-length preservation, cleared pending updates, and idempotence proved under the relevant default-map laws; content preservation still needs bulk-update content proofs for Tree and ProgressiveTree |
| `iter`, `iter_from`, `IntoIterator` | Enumerate the merged sequence/suffix; reject invalid starting indices | Pending iterator extraction and invariants |
| `ProgressiveListIter::next`, `size_hint`, `ExactSizeIterator::len` | Yield the next merged element; exact remaining length; exhaustion | Pending |
| `iter_cow`, `iter_cow_from`, `ProgressiveListIterCow::next_cow` | Enumerate mutable handles at successive indices; read-only and write-back behavior; exhaustion | Pending |
| `to_vec` | Return the merged sequence in order | Pending iteration proof and element-clone law |
| `pop_front` | Drop the specified prefix, reindex remaining values; reject oversized drops unchanged | Pending construction and iteration proofs |
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
- `Tree/ProgressiveTree.lean`: exact routing to binary-tree lookups, plus
  selected-subtree density and update read-back lemmas.
- `Tree/ProgressiveList.lean`: pending/backing lookup behavior and push/read-back
  at all query indices, conditional only on the relevant insertion law.
- `Tree/PackedLeaf/Contents.lean`, `Tree/PackedLeaf/BulkUpdate.lean`: exact
  packed insertion contents and bulk-update window contents, including initial
  cloning and the complete scan. Pending values override their own slots;
  absent updates preserve the previous values. No density or map metadata
  assumptions are needed for these successful-execution content results.
- `Tree/BulkUpdate.lean`: unpacked-leaf bulk-update contents and lookup
  read-back. Binary node recursion, zero expansion, and the corresponding
  progressive-tree content theorem remain outstanding.

## Validation

For each completed piece: build its Lean module, check the assumptions, and
commit with signing disabled and a model co-author trailer. Before completion:
regenerate the full extraction, build all proof modules, inspect axiom
dependencies for admissions, run the relevant Rust tests and formatting checks,
and audit every row above against concrete theorem statements.

## Rust corrections

- `0352f19`: `ProgressiveListIterCow::next_cow` advances its cursor only when
  yielding a handle. Exhaustion no longer increments indefinitely and eventually
  overflows. A regression test exercises the `usize::MAX` exhausted cursor in
  release mode; the Lean iterator correctness proof remains outstanding.
