# Dense-tree preservation roadmap

The central representation judgment is:

```lean
DenseTree packing_factor tree depth len
```

paired with:

```lean
PackingLayout ValueInst packing_factor packing_depth
```

`DenseTree` means that the materialized values form exactly one left prefix;
all remaining capacity is represented by `Zero` padding.

## Basic derived lemmas

- [x] `DenseTree` has a unique depth and length for fixed packing/tree
      (`DenseTree.indices_unique`).
- [x] A dense tree's length is at most `subtreeCapacity`
      (`DenseTree.length_le_capacity`).
- [x] `Tree.compute_len` returns the `DenseTree` length when represented by a
      supplied `Usize` (`DenseTree.compute_len_eq`).
- [x] Length zero implies the tree is the canonical `Zero depth`
      (`DenseTree.eq_zero_of_length_zero`).
- [x] Full length implies that the tree contains no `Zero` padding
      (`DenseTree.noZero_of_full`).
- [ ] For `index < len`, `get_recursive` returns a materialized value.
- [ ] For `len <= index < capacity`, `get_recursive` returns `none`.
- [x] `DenseTree` plus `index <= len` implies
      `updateIndexWithinLength`, discharging the roundtrip side condition
      (`DenseTree.updateIndexWithinLength`,
      `get_recursive_with_updated_leaf_dense`).

## Constructors

- [x] `Tree.zero` produces a dense tree of length zero
      (`zero_preserves_dense`).
- [x] `Tree.empty` produces a dense tree of length zero
      (`empty_preserves_dense`).
- [x] `Tree.zero_unboxed` produces a dense tree of length zero
      (`zero_unboxed_preserves_dense`).
- [x] `Tree.leaf`, `leaf_with_hash`, and `leaf_unboxed` produce an unpacked
      dense tree of length one (`leaf_preserves_dense`,
      `leaf_with_hash_preserves_dense`, `leaf_unboxed_preserves_dense`).
- [x] `PackedLeaf.single` produces a packed dense tree of length one under a
      packed `PackingLayout` (`packedLeaf_single_preserves_dense`).
- [x] `Tree.node` and `node_unboxed` preserve density when their child lengths
      satisfy the left-prefix condition (`node_preserves_dense`,
      `node_unboxed_preserves_dense`).

## Updates

- [x] `PackedLeaf.insert_at_index` preserves the packed-leaf length for a
      replacement and increments it for a one-past-the-end insertion
      (`packedLeaf_insert_at_index_preserves_dense`).
- [ ] `Tree.with_updated_leaf` preserves `DenseTree`: `index < len` preserves
      the length, while `index = len` increments it.
- [ ] Derive `get_recursive_with_updated_leaf_general` from `DenseTree` and
      `index <= len`, removing its local side condition from caller proofs.
- [ ] Define a dense update-map predicate: updates below the old length are
      replacements and extensions cover the complete interval
      `[old_len, new_len)`.
- [ ] Once `with_updated_leaves` is included in the extracted subset, prove it
      preserves `DenseTree` under the dense update-map predicate.

## Builders and container boundaries

- [ ] Once extracted, prove `Builder::push`, `push_node`, and `finish` preserve
      the builder stack invariant and return a `DenseTree` at the reported
      length.
- [ ] Prove `repeat_list`, list/vector construction, decoding, and `pop_front`
      return dense backing trees.
- [ ] Define the `Interface` invariant for pending updates, including the
      contiguous-extension condition needed by `bulk_update`.
- [ ] Connect cached list/vector length and depth fields to `DenseTree`.

## Structural sharing

- [ ] `Tree.rebase_on` preserves density when both inputs are dense at their
      supplied logical lengths.
- [ ] Strengthen `Tree.intra_rebase` so replacement candidates carry equal
      represented lengths, then prove it preserves density. The current
      `(depth, hash)` key does not by itself imply equal length for zero-valued
      subtrees.

## Packing and machine arithmetic

- [ ] Establish `PackingLayout` for each concrete translated `Value` instance
      used by verified containers.
- [ ] Prove packing factors are positive and routing shifts fit in `Usize`.
- [ ] Bridge `subtreeCapacity` to `1 << (depth + packing_depth)` using
      `factor_is_power`.
