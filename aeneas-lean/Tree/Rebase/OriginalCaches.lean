import Tree.Rebase.Kind

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Original cache validity only where the input-based action retains caches.
A no-op retains the entire original tree. Whole-base replacement retains none.
A rebuilt node retains its original root cache and selected child caches.
Validity needed to justify hash shortcuts is a separate input law. -/
def Tree.RebaseOrigCachesOn {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat) : Prop :=
  match orig.rebaseKind inst base with
  | .equalReplace => True
  | .notEqualReplace =>
      match orig, base with
      | .Node hash left right, .Node _ baseLeft baseRight =>
          P (.binary depth (left.elements ++ right.elements)) hash ∧
            left.RebaseOrigCachesOn inst P baseLeft (depth - 1) ∧
              right.RebaseOrigCachesOn inst P baseRight (depth - 1)
      | _, _ => True
  | .notEqualNoop | .equalNoop => orig.CachesOn P depth

/-- Full original validity supplies the retained-cache scope. -/
theorem Tree.rebaseOrigCachesOn_of_caches {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat)
    (horig : orig.CachesOn P depth) : orig.RebaseOrigCachesOn inst P base depth := by
  induction orig generalizing base depth with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    cases base <;> rw [Tree.RebaseOrigCachesOn.eq_def] <;> split <;> trivial
  | Node hash left right ihleft ihright =>
    cases base with
    | Leaf leaf | PackedLeaf leaf | Zero level =>
      rw [Tree.RebaseOrigCachesOn.eq_def]
      split <;> trivial
    | Node baseHash baseLeft baseRight =>
      rw [Tree.RebaseOrigCachesOn.eq_def]
      split
      · trivial
      · exact ⟨horig.1, ihleft baseLeft (depth - 1) horig.2.1,
          ihright baseRight (depth - 1) horig.2.2⟩
      · exact horig
      · exact horig

/-- No-op actions retain every original cache. -/
theorem Tree.RebaseOrigCachesOn.orig_of_noop {T : Type}
    {inst : core.cmp.PartialEq T T} {P : CacheSubject T → CacheHash → Prop}
    {orig base : Tree T} {depth : Nat} (hcache : orig.RebaseOrigCachesOn inst P base depth)
    (hkind : orig.rebaseKind inst base = .notEqualNoop ∨ orig.rebaseKind inst base = .equalNoop) :
    orig.CachesOn P depth := by
  rcases hkind with hkind | hkind <;>
    simpa only [Tree.RebaseOrigCachesOn.eq_def, hkind] using hcache

/-- Whole-base replacement requires no validity of the discarded original. -/
theorem Tree.rebaseOrigCachesOn_of_equal_replace {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat)
    (hkind : orig.rebaseKind inst base = .equalReplace) :
    orig.RebaseOrigCachesOn inst P base depth := by
  simp only [Tree.RebaseOrigCachesOn.eq_def, hkind]

/-- Every retained or rebuilt node supplies its root cache and the original
cache scopes for both children. No branch, execution, or metadata law is used. -/
theorem Tree.RebaseOrigCachesOn.node_kept {T : Type}
    {inst : core.cmp.PartialEq T T} {P : CacheSubject T → CacheHash → Prop}
    {hash baseHash : CacheHash} {left right baseLeft baseRight : Tree T} {depth : Nat}
    (hcache : (Tree.Node hash left right).RebaseOrigCachesOn inst P
      (.Node baseHash baseLeft baseRight) depth)
    (hkeep : (Tree.Node hash left right).rebaseKind inst (.Node baseHash baseLeft baseRight) ≠ .equalReplace) :
    P (.binary depth (left.elements ++ right.elements)) hash ∧
      left.RebaseOrigCachesOn inst P baseLeft (depth - 1) ∧
        right.RebaseOrigCachesOn inst P baseRight (depth - 1) := by
  rw [Tree.RebaseOrigCachesOn.eq_def] at hcache
  cases hkind : (Tree.Node hash left right).rebaseKind inst (.Node baseHash baseLeft baseRight) <;>
    simp only [hkind] at hcache hkeep
  all_goals solve
    | exact hcache
    | exact ⟨hcache.1, left.rebaseOrigCachesOn_of_caches inst P baseLeft (depth - 1) hcache.2.1,
        right.rebaseOrigCachesOn_of_caches inst P baseRight (depth - 1) hcache.2.2⟩
    | exact (hkeep rfl).elim

end milhouse.tree
