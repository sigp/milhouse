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

- [ ] `DenseTree` has a unique depth and length for fixed packing/tree.
- [ ] A dense tree's length is at most `subtreeCapacity`.
- [ ] `Tree.compute_len` returns the `DenseTree` length (including the required
      `Usize` no-overflow bridge).
- [ ] Length zero implies the tree is the canonical `Zero depth`.
- [ ] Full length implies that the tree contains no `Zero` padding.
- [ ] For `index < len`, `get_recursive` returns a materialized value.
- [ ] For `len <= index < capacity`, `get_recursive` returns `none`.
- [ ] `DenseTree` plus `index <= len` implies
      `updateIndexWithinLength`, discharging the roundtrip side condition.

## Constructors

- [x] `Tree.zero` produces a dense tree of length zero
      (`zero_preserves_dense`).
- [ ] `Tree.empty` produces a dense tree of length zero.
- [ ] `Tree.zero_unboxed` produces a dense tree of length zero.
- [ ] `Tree.leaf`, `leaf_with_hash`, and `leaf_unboxed` produce an unpacked
      dense tree of length one.
- [ ] `PackedLeaf.single` produces a packed dense tree of length one under a
      packed `PackingLayout`.
- [ ] `Tree.node` and `node_unboxed` preserve density when their child lengths
      satisfy the left-prefix condition.

## Updates

- [ ] `PackedLeaf.insert_at_index` preserves the packed-leaf length for a
      replacement and increments it for a one-past-the-end insertion.
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
