import Tree.HashCache.Collisions
import Tree.ProgressiveTree.Rebase.Contents
import Tree.ProgressiveTree.Rebase.CacheInputs
import Tree.ProgressiveTree.Rebase.HashInputs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- The finite binary hash-input pairs at corresponding progressive layers.
Progressive caches are omitted because rebasing does not compare them. -/
noncomputable def ProgressiveTree.rebaseHashInputs {T : Type}
    (orig base : ProgressiveTree T) (depth : Nat) : _root_.List (BinaryHashInputPair T) := by
  classical
  exact match orig, base with
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight =>
      if triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
          (.ProgressiveNode baseHash baseLeft baseRight) = ok false then
        left.rebaseHashInputs baseLeft (2 * depth) ++ right.rebaseHashInputs baseRight (depth + 1)
      else []
  | _, _ => []

theorem ProgressiveTree.rebaseHashInputs_eq_nil_of_cleared {T : Type}
    (orig base : ProgressiveTree T) (depth : Nat) (hclear : orig.CachesCleared) :
    orig.rebaseHashInputs base depth = [] := by
  induction orig generalizing base depth with
  | ProgressiveZero => rfl
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => rfl
    | ProgressiveNode baseHash baseLeft baseRight =>
      simp [ProgressiveTree.rebaseHashInputs,
        tree.Tree.rebaseHashInputs_eq_nil_of_cleared left baseLeft (2 * depth) hclear.2.1,
        ih baseRight (depth + 1) hclear.2.2]

theorem ProgressiveTree.cachedHashesAgree_of_cleared {T : Type}
    (orig base : ProgressiveTree T) (hclear : orig.CachesCleared) :
    orig.CachedHashesAgree base := by
  induction orig generalizing base with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      intro _
      exact ⟨tree.Tree.cachedHashesAgree_of_cleared left baseLeft hclear.2.1,
        ih baseRight hclear.2.2⟩

/-- Original cache validity at reached binary hash shortcuts, selected base
validity, and the finite reference collision law establish all operational
hash-shortcut obligations. Neither tree's progressive cache validity, shape,
or packing layout is required by this bridge. -/
theorem ProgressiveTree.cachedHashesAgree_of_valid_caches {T : Type}
    (inst : core.cmp.PartialEq T T) (reference : CacheSubject T → CacheHash)
    (orig base : ProgressiveTree T) (depth : Nat)
    (horig : orig.RebaseHashCachesOn (CacheValidFor reference) base depth)
    (hbase : orig.RebaseBaseCachesOn inst (CacheValidFor reference) base depth)
    (hcollisions : BinaryHashCollisionSoundOn reference (orig.rebaseHashInputs base depth)) :
    orig.CachedHashesAgree base := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      intro hpointer
      simp only [ProgressiveTree.rebaseHashInputs, hpointer, ↓reduceIte] at hcollisions
      exact ⟨tree.Tree.cachedHashesAgree_of_valid_caches inst reference left baseLeft (2 * depth)
          (horig hpointer).1 (hbase hpointer).1 (hcollisions.mono (fun pair hpair => List.mem_append_left _ hpair)),
        ih baseRight (depth + 1) (horig hpointer).2 (hbase hpointer).2
          (hcollisions.mono (fun pair hpair => List.mem_append_right _ hpair))⟩

end milhouse.progressive_tree
