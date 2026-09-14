import Tree.ProgressiveTree.HashCache
import Tree.Rebase.OriginalCaches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Original cache validity along the actual progressive traversal. Missing
or shared input retains the entire original suffix. Otherwise each original
progressive cache is retained, while the binary action selects the original
caches kept in that layer. Hash-shortcut validity is a separate input law. -/
def ProgressiveTree.RebaseOrigCachesOn {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) : ProgressiveTree T → ProgressiveTree T → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight, depth =>
      (triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
        P (.progressive depth (left.elements ++ right.elements)) hash ∧
          left.RebaseOrigCachesOn inst P baseLeft (2 * depth) ∧
            right.RebaseOrigCachesOn inst P baseRight (depth + 1)) ∧
      (triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) ≠ ok false →
        (ProgressiveTree.ProgressiveNode hash left right).CachesOn P depth)
  | orig, _, depth => orig.CachesOn P depth

/-- Full original validity implies validity of all retained original caches. -/
theorem ProgressiveTree.rebaseOrigCachesOn_of_caches {T : Type}
    (inst : core.cmp.PartialEq T T) (P : CacheSubject T → CacheHash → Prop)
    (orig base : ProgressiveTree T) (depth : Nat) (horig : orig.CachesOn P depth) :
    orig.RebaseOrigCachesOn inst P base depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => exact horig
    | ProgressiveNode baseHash baseLeft baseRight =>
      exact ⟨fun _ => ⟨horig.1,
          left.rebaseOrigCachesOn_of_caches inst P baseLeft (2 * depth) horig.2.1,
          ih baseRight (depth + 1) horig.2.2⟩, fun _ => horig⟩

/-- Every immediate missing/shared-input stop retains the full original
suffix, so its input scope supplies the complete original cache invariant. -/
theorem ProgressiveTree.RebaseOrigCachesOn.orig_of_stop {T : Type}
    {inst : core.cmp.PartialEq T T} {P : CacheSubject T → CacheHash → Prop}
    {orig base : ProgressiveTree T} {depth : Nat}
    (hcache : orig.RebaseOrigCachesOn inst P base depth)
    (hstop : orig = .ProgressiveZero ∨ base = .ProgressiveZero ∨
      triomphe.arc.Arc.ptr_eq orig base = ok true) : orig.CachesOn P depth := by
  rcases hstop with horig | hbase | hpointer
  · subst orig
    trivial
  · subst base
    cases orig <;> exact hcache
  · cases orig <;> cases base
    all_goals first
      | exact hcache
      | exact hcache.2 (by simp [hpointer])

end milhouse.progressive_tree
