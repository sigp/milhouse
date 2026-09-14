import Tree.HashCache.Validity
import Tree.ProgressiveTree.HashCache

open Aeneas Aeneas.Std Result

namespace milhouse

/-- Every physically stored binary-tree cache is the zero sentinel. Zero
subtrees contain no stored cache. This property is independent of shape and
depth, so it can be tracked while a builder assembles its forest. -/
def tree.Tree.CachesCleared {T : Type} : tree.Tree T → Prop
  | .Leaf leaf => leaf.hash = Array.repeat 32#usize 0#u8
  | .PackedLeaf leaf => leaf.hash = Array.repeat 32#usize 0#u8
  | .Node hash left right =>
      hash = Array.repeat 32#usize 0#u8 ∧ left.CachesCleared ∧ right.CachesCleared
  | .Zero _ => True

/-- Cleared caches satisfy any cache predicate that accepts invalidation,
at every depth and for arbitrary stored values. -/
theorem tree.Tree.CachesCleared.cachesOn {T : Type}
    {self : tree.Tree T} (hself : self.CachesCleared)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8)) (depth : Nat) :
    self.CachesOn P depth := by
  induction self generalizing depth with
  | Leaf leaf => change P _ leaf.hash; rw [hself]; exact hzero _
  | PackedLeaf leaf => change P _ leaf.hash; rw [hself]; exact hzero _
  | Node hash left right ihleft ihright =>
    exact ⟨by rw [hself.1]; exact hzero _, ihleft hself.2.1 _, ihright hself.2.2 _⟩
  | Zero depth => trivial

def progressive_tree.ProgressiveTree.CachesCleared {T : Type} :
    progressive_tree.ProgressiveTree T → Prop
  | .ProgressiveZero => True
  | .ProgressiveNode hash left right =>
      hash = Array.repeat 32#usize 0#u8 ∧ left.CachesCleared ∧ right.CachesCleared

theorem progressive_tree.ProgressiveTree.CachesCleared.cachesOn {T : Type}
    {self : progressive_tree.ProgressiveTree T} (hself : self.CachesCleared)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8)) (depth : Nat) :
    self.CachesOn P depth := by
  induction self generalizing depth with
  | ProgressiveZero => trivial
  | ProgressiveNode hash left right ih =>
    exact ⟨by rw [hself.1]; exact hzero _, hself.2.1.cachesOn P hzero _, ih hself.2.2 _⟩

end milhouse
