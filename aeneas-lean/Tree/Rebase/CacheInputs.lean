import Tree.Rebase.Kind

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Validity of base caches selected by the input-based action category.
No-op results need no base cache. Whole-base replacement needs all base caches;
a rebuilt node needs only the base caches selected by its child rebases.
This constrains stored input caches, without assuming an output invariant. -/
def Tree.RebaseBaseCachesOn {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat) : Prop :=
  match orig.rebaseKind inst base with
  | .equalReplace => base.CachesOn P depth
  | .notEqualReplace =>
      match orig, base with
      | .Node _ left right, .Node _ baseLeft baseRight =>
          left.RebaseBaseCachesOn inst P baseLeft (depth - 1) ∧
            right.RebaseBaseCachesOn inst P baseRight (depth - 1)
      | _, _ => True
  | .notEqualNoop | .equalNoop => True

/-- Full base validity implies the weaker selected-cache input law. -/
theorem Tree.rebaseBaseCachesOn_of_caches {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat)
    (hbase : base.CachesOn P depth) : orig.RebaseBaseCachesOn inst P base depth := by
  induction orig generalizing base depth with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    cases base <;> rw [Tree.RebaseBaseCachesOn.eq_def] <;> split <;> trivial
  | Node hash left right ihleft ihright =>
    cases base with
    | Leaf leaf | PackedLeaf leaf | Zero level =>
      rw [Tree.RebaseBaseCachesOn.eq_def]
      split <;> trivial
    | Node baseHash baseLeft baseRight =>
      rw [Tree.RebaseBaseCachesOn.eq_def]
      split
      · exact hbase
      · exact ⟨ihleft baseLeft (depth - 1) hbase.2.1, ihright baseRight (depth - 1) hbase.2.2⟩
      · trivial
      · trivial

/-- Whole-base replacement exposes exactly the full base-cache premise. -/
theorem Tree.RebaseBaseCachesOn.base_of_equal_replace {T : Type}
    {inst : core.cmp.PartialEq T T} {P : CacheSubject T → CacheHash → Prop}
    {orig base : Tree T} {depth : Nat} (hcache : orig.RebaseBaseCachesOn inst P base depth)
    (hkind : orig.rebaseKind inst base = .equalReplace) : base.CachesOn P depth := by
  simpa only [Tree.RebaseBaseCachesOn.eq_def, hkind] using hcache

/-- A no-op category needs no base validity, including when the base contains
invalid caches in otherwise matching subtrees. -/
theorem Tree.rebaseBaseCachesOn_of_noop {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat)
    (hkind : orig.rebaseKind inst base = .notEqualNoop ∨ orig.rebaseKind inst base = .equalNoop) :
    orig.RebaseBaseCachesOn inst P base depth := by
  rcases hkind with hkind | hkind <;> simp only [Tree.RebaseBaseCachesOn.eq_def, hkind]

/-- After both outer shortcuts are rejected, the parent's selected-cache law
supplies the child laws. Whole-base validity supplies both; rebuilt nodes
require them directly; no-op parents have no-op children. -/
theorem Tree.RebaseBaseCachesOn.children {T : Type}
    {inst : core.cmp.PartialEq T T} {P : CacheSubject T → CacheHash → Prop}
    {hash baseHash : CacheHash} {left right baseLeft baseRight : Tree T} {depth : Nat}
    (hcache : (Tree.Node hash left right).RebaseBaseCachesOn inst P
      (.Node baseHash baseLeft baseRight) depth)
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hdescend : ¬ RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
      (baseLeft.elements ++ baseRight.elements).length) :
    left.RebaseBaseCachesOn inst P baseLeft (depth - 1) ∧
      right.RebaseBaseCachesOn inst P baseRight (depth - 1) := by
  rw [Tree.RebaseBaseCachesOn.eq_def,
    Tree.rebaseKind_of_descend _ _ _ _ _ _ _ hpointer hdescend] at hcache
  cases hleft : left.rebaseKind inst baseLeft <;> cases hright : right.rebaseKind inst baseRight <;>
    simp only [hleft, hright, RebaseKind.combine] at hcache
  all_goals solve
    | exact hcache
    | exact ⟨left.rebaseBaseCachesOn_of_caches inst P baseLeft (depth - 1) hcache.2.1,
        right.rebaseBaseCachesOn_of_caches inst P baseRight (depth - 1) hcache.2.2⟩
    | (constructor <;> simp only [Tree.RebaseBaseCachesOn.eq_def, hleft, hright])

end milhouse.tree
