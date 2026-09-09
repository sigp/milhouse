import Tree.ProgressiveTree.HashCache

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Base binary-cache validity at the progressive layers selected by rebasing.
An absent layer on either side stops traversal, and pointer sharing skips the
complete shared suffix. Base progressive caches are never imported. This is
an input invariant, independent of an assumed execution or output tree. -/
def ProgressiveTree.RebaseBaseCachesOn {T : Type} (P : CacheSubject T → CacheHash → Prop) :
    ProgressiveTree T → ProgressiveTree T → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight, depth =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      baseLeft.CachesOn P (2 * depth) ∧ right.RebaseBaseCachesOn P baseRight (depth + 1)
  | _, _, _ => True

/-- Validity of all base binary caches supplies the weaker selected-layer law.
No validity, shape, packing, or comparison law for the original is needed. -/
theorem ProgressiveTree.rebaseBaseCachesOn_of_binary {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig base : ProgressiveTree T) (depth : Nat)
    (hbase : base.BinaryCachesOn P depth) : orig.RebaseBaseCachesOn P base depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      exact fun _ => ⟨hbase.1, ih baseRight (depth + 1) hbase.2⟩

/-- Full base cache validity also supplies the selected binary-layer law. -/
theorem ProgressiveTree.rebaseBaseCachesOn_of_caches {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig base : ProgressiveTree T) (depth : Nat)
    (hbase : base.CachesOn P depth) : orig.RebaseBaseCachesOn P base depth :=
  orig.rebaseBaseCachesOn_of_binary P base depth hbase.binary

/-- A shared progressive suffix needs no separate validity premise for the
base: the pointer contract identifies it with the original retained suffix. -/
theorem ProgressiveTree.rebaseBaseCachesOn_of_ptr_eq {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig base : ProgressiveTree T) (depth : Nat)
    (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseBaseCachesOn P base depth := by
  cases orig <;> cases base <;> simp [ProgressiveTree.RebaseBaseCachesOn, hpointer]

/-- Any base suffix beyond the original's last layer has no cache obligation. -/
@[simp] theorem ProgressiveTree.rebaseBaseCachesOn_zero_left {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (base : ProgressiveTree T) (depth : Nat) :
    ProgressiveTree.ProgressiveZero.RebaseBaseCachesOn P base depth := by
  cases base <;> trivial

/-- An exhausted base contributes no cache obligation for the original suffix. -/
@[simp] theorem ProgressiveTree.rebaseBaseCachesOn_zero_right {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig : ProgressiveTree T) (depth : Nat) :
    orig.RebaseBaseCachesOn P .ProgressiveZero depth := by
  cases orig <;> trivial

end milhouse.progressive_tree
