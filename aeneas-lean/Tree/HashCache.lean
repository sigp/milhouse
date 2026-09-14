import Tree.Contents

open Aeneas Aeneas.Std Result

namespace milhouse

/-- The logical data associated with a cache. Binary depth distinguishes
different amounts of padding; progressive depth identifies the suffix's layer
geometry. The packing layout is fixed when a cache predicate is chosen. -/
inductive CacheSubject (T : Type) where
  | leaf (value : T)
  | packed (values : _root_.List T)
  | binary (depth : Nat) (values : _root_.List T)
  | progressive (depth : Nat) (values : _root_.List T)

abbrev CacheHash := alloy_primitives.bits.fixed.FixedBytes 32#usize

namespace tree

/-- Every stored cache satisfies a predicate relating its hash to its logical
input. This includes zero caches: a semantic validity predicate can accept the
zero sentinel unconditionally. No hash computation or collision law is built
into this invariant. Zero subtrees have no stored cache. -/
def Tree.CachesOn {T : Type} (P : CacheSubject T → CacheHash → Prop) : Tree T → Nat → Prop
  | .Leaf leaf, _ => P (.leaf leaf.value) leaf.hash
  | .PackedLeaf leaf, _ => P (.packed leaf.values.val) leaf.hash
  | .Node hash left right, depth =>
      P (.binary depth (left.elements ++ right.elements)) hash ∧
        left.CachesOn P (depth - 1) ∧ right.CachesOn P (depth - 1)
  | .Zero _, _ => True

end tree
end milhouse
