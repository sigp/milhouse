import Tree.HashCache
import Tree.ProgressiveTree.Density

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- The cache predicate holds for every progressive suffix and every cache
inside its binary layers, at their actual depths. Pending updates are not
part of these cache inputs; they have not yet been applied to the tree. -/
def ProgressiveTree.CachesOn {T : Type} (P : CacheSubject T → CacheHash → Prop) :
    ProgressiveTree T → Nat → Prop
  | .ProgressiveZero, _ => True
  | .ProgressiveNode hash left right, depth =>
      P (.progressive depth (left.elements ++ right.elements)) hash ∧
        left.CachesOn P (2 * depth) ∧ right.CachesOn P (depth + 1)

/-- Only the binary-layer caches. Progressive rebasing may import these from
the base, but always retains the original progressive-node caches. -/
def ProgressiveTree.BinaryCachesOn {T : Type} (P : CacheSubject T → CacheHash → Prop) :
    ProgressiveTree T → Nat → Prop
  | .ProgressiveZero, _ => True
  | .ProgressiveNode _ left right, depth =>
      left.CachesOn P (2 * depth) ∧ right.BinaryCachesOn P (depth + 1)

theorem ProgressiveTree.CachesOn.binary {T : Type}
    {P : CacheSubject T → CacheHash → Prop} {self : ProgressiveTree T} {depth : Nat}
    (hself : self.CachesOn P depth) : self.BinaryCachesOn P depth := by
  induction self generalizing depth with
  | ProgressiveZero => trivial
  | ProgressiveNode hash left right ih => exact ⟨hself.2.1, ih hself.2.2⟩

end milhouse.progressive_tree
