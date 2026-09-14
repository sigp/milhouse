import Tree.Rebase.SelectedCacheInputs
import Tree.ProgressiveTree.Rebase.ContentInputs
import Tree.ProgressiveTree.Rebase.OriginalCaches
import Tree.ProgressiveTree.Rebase.CacheInputs

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Retained cache obligations at the actual progressive metadata. Missing
or shared inputs retain the original suffix. Entered layers retain the
original progressive root and select binary caches using the actual packing
queries and clamped lengths. Base progressive caches are never imported.
The predicate assumes neither query success nor an output tree. -/
def ProgressiveTree.RebaseCacheInputs {T : Type} (ValueInst : Value T)
    (P : CacheSubject T → CacheHash → Prop) :
    ProgressiveTree T → ProgressiveTree T → Nat → Nat → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight,
      origLength, baseLength, depth =>
      (triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
        ∀ factor packingDepth, RebasePackingQueries ValueInst.tree_hashTreeHashInst factor packingDepth →
        P (.progressive depth (left.elements ++ right.elements)) hash ∧
          left.RebaseCacheInputs ValueInst.corecmpPartialEqInst P baseLeft
            (some (rebaseLayerLength factor origLength depth, rebaseLayerLength factor baseLength depth))
            (2 * depth + packingDepth.val) (2 * depth) ∧
          right.RebaseCacheInputs ValueInst P baseRight origLength baseLength (depth + 1)) ∧
      (triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) ≠ ok false →
        (ProgressiveTree.ProgressiveNode hash left right).CachesOn P depth)
  | orig, _, _, _, depth => orig.CachesOn P depth

/-- An immediate stop requires exactly the original suffix's caches, with
no packing queries or base-cache obligations. -/
theorem ProgressiveTree.rebaseCacheInputs_iff_of_stop {T : Type} (ValueInst : Value T)
    (P : CacheSubject T → CacheHash → Prop)
    (orig base : ProgressiveTree T) (origLength baseLength depth : Nat)
    (hstop : orig = .ProgressiveZero ∨ base = .ProgressiveZero ∨
      triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseCacheInputs ValueInst P base origLength baseLength depth ↔ orig.CachesOn P depth := by
  rcases hstop with horig | hbase | hpointer
  · subst orig
    cases base <;> rfl
  · subst base
    cases orig <;> rfl
  · cases orig <;> cases base <;> simp [ProgressiveTree.RebaseCacheInputs, hpointer]

/-- On dense representable inputs, query uniqueness and removal of machine
clamps identify this scope with the existing original/base cache laws. -/
theorem ProgressiveTree.rebaseCacheInputs_iff_of_dense {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base : ProgressiveTree T} {origLength baseLength depth : Nat}
    (horig : orig.Dense factor depth (origLength - progressiveCapacity factor depth))
    (hbase : base.Dense factor depth (baseLength - progressiveCapacity factor depth))
    (hfit : orig.Fits factor depth) :
    orig.RebaseCacheInputs ValueInst P base origLength baseLength depth ↔
      orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth ∧
        orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> simp [ProgressiveTree.RebaseCacheInputs,
      ProgressiveTree.RebaseOrigCachesOn, ProgressiveTree.RebaseBaseCachesOn]
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => simp [ProgressiveTree.RebaseCacheInputs,
        ProgressiveTree.RebaseOrigCachesOn, ProgressiveTree.RebaseBaseCachesOn]
    | ProgressiveNode baseHash baseLeft baseRight =>
      have hleftIff := tree.Tree.rebaseCacheInputs_iff_of_dense ValueInst hlayout P rfl
        horig.split_layer.1 hbase.split_layer.1
      have hrightIff := ih horig.right_remainder hbase.right_remainder hfit.2
      by_cases hpointer : triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
          (.ProgressiveNode baseHash baseLeft baseRight) = ok false
      · simp [ProgressiveTree.RebaseCacheInputs, ProgressiveTree.RebaseOrigCachesOn,
          ProgressiveTree.RebaseBaseCachesOn, hpointer]
        constructor
        · intro hcache
          obtain ⟨hroot, hleft, hright⟩ := hcache factor packingDepth (RebasePackingQueries.of_layout hlayout)
          rw [rebaseLayerLength_of_fits hlayout origLength depth hfit.1,
            rebaseLayerLength_of_fits hlayout baseLength depth hfit.1] at hleft
          obtain ⟨hleftOrig, hleftBase⟩ := hleftIff.mp hleft
          obtain ⟨hrightOrig, hrightBase⟩ := hrightIff.mp hright
          exact ⟨hroot, hleftOrig, hrightOrig, hleftBase, hrightBase⟩
        · rintro ⟨hroot, hleftOrig, hrightOrig, hleftBase, hrightBase⟩ actualFactor actualDepth hqueries
          obtain ⟨rfl, rfl⟩ := hqueries.unique (RebasePackingQueries.of_layout hlayout)
          refine ⟨hroot, ?_, hrightIff.mpr ⟨hrightOrig, hrightBase⟩⟩
          rw [rebaseLayerLength_of_fits hlayout origLength depth hfit.1,
            rebaseLayerLength_of_fits hlayout baseLength depth hfit.1]
          exact hleftIff.mpr ⟨hleftOrig, hleftBase⟩
      · simp [ProgressiveTree.RebaseCacheInputs, ProgressiveTree.RebaseOrigCachesOn,
          ProgressiveTree.RebaseBaseCachesOn, hpointer]

end milhouse.progressive_tree
