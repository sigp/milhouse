import Tree.ProgressiveTree.HashCache
import Tree.Rebase.HashInputs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Original hash-shortcut laws within reached progressive layers. Missing
and shared suffixes need none; progressive-node caches are never compared. -/
def ProgressiveTree.RebaseHashCachesOn {T : Type} (P : CacheSubject T → CacheHash → Prop) :
    ProgressiveTree T → ProgressiveTree T → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight, depth =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      left.RebaseHashCachesOn P baseLeft (2 * depth) ∧
        right.RebaseHashCachesOn P baseRight (depth + 1)
  | _, _, _ => True

/-- Original binary-cache validity supplies all selected hash-shortcut laws. -/
theorem ProgressiveTree.rebaseHashCachesOn_of_binary {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig base : ProgressiveTree T) (depth : Nat)
    (horig : orig.BinaryCachesOn P depth) : orig.RebaseHashCachesOn P base depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      exact fun _ => ⟨left.rebaseHashCachesOn_of_caches P baseLeft (2 * depth) horig.1,
        ih baseRight (depth + 1) horig.2⟩

/-- Full original cache validity also supplies the selected hash laws. -/
theorem ProgressiveTree.rebaseHashCachesOn_of_caches {T : Type}
    (P : CacheSubject T → CacheHash → Prop) (orig base : ProgressiveTree T) (depth : Nat)
    (horig : orig.CachesOn P depth) : orig.RebaseHashCachesOn P base depth :=
  orig.rebaseHashCachesOn_of_binary P base depth horig.binary

end milhouse.progressive_tree
