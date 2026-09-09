import Tree.Rebase.HashShortcut

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Original cache laws only at nonzero hash shortcuts reached by rebasing.
Pointer sharing skips the subtree. A hash shortcut needs its original root
cache law, and omits descendants. Otherwise only corresponding children are
visited. These caches justify content equality, independently of retention. -/
def Tree.RebaseHashCachesOn {T : Type} (P : CacheSubject T → CacheHash → Prop) :
    Tree T → Tree T → Nat → Prop
  | .Node hash left right, .Node baseHash baseLeft baseRight, depth =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T)
        (.Node baseHash baseLeft baseRight) = ok false →
      (RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
        (baseLeft.elements ++ baseRight.elements).length →
        P (.binary depth (left.elements ++ right.elements)) hash) ∧
      (¬ RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
        (baseLeft.elements ++ baseRight.elements).length →
        left.RebaseHashCachesOn P baseLeft (depth - 1) ∧
          right.RebaseHashCachesOn P baseRight (depth - 1))
  | _, _, _ => True

/-- Full original validity supplies every selected hash-comparison law. -/
theorem Tree.rebaseHashCachesOn_of_caches {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T) (depth : Nat)
    (horig : orig.CachesOn P depth) : orig.RebaseHashCachesOn P base depth := by
  induction orig generalizing base depth with
  | Leaf leaf | PackedLeaf leaf | Zero level => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base with
    | Leaf leaf | PackedLeaf leaf | Zero level => trivial
    | Node baseHash baseLeft baseRight =>
      exact fun _ => ⟨fun _ => horig.1, fun _ =>
        ⟨ihleft baseLeft (depth - 1) horig.2.1, ihright baseRight (depth - 1) horig.2.2⟩⟩

end milhouse.tree
