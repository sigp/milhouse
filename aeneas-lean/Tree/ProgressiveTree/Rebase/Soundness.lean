import Tree.Rebase.Soundness

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_tree

/-- Rebase equality soundness on corresponding binary layers. Missing suffix
layers require no element law; progressive caches are never compared. -/
def ProgressiveTree.RebaseEqualitySound {T : Type} (inst : core.cmp.PartialEq T T) :
    ProgressiveTree T → ProgressiveTree T → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      left.RebaseEqualitySound inst baseLeft ∧ right.RebaseEqualitySound inst baseRight
  | _, _ => True

/-- Ordinary global comparison soundness specializes to the actual input
layers. Public rebase specifications need only the resulting scoped law. -/
theorem ProgressiveTree.rebaseEqualitySound_of_sound {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ left right, inst.eq left right = ok true → left = right)
    (hne : ∀ left right, inst.ne left right = ok false → left = right)
    (orig base : ProgressiveTree T) : orig.RebaseEqualitySound inst base := by
  induction orig generalizing base with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      exact fun _ => ⟨left.rebaseEqualitySound_of_sound inst heq hne baseLeft, ih baseRight⟩

/-- Corresponding binary layer caches agree where rebasing can compare them.
    Progressive-node hashes are ignored because this operation never uses them
    to establish equality. -/
def ProgressiveTree.CachedHashesAgree {T : Type} : ProgressiveTree T → ProgressiveTree T → Prop
  | .ProgressiveNode hash origLeft origRight, .ProgressiveNode baseHash baseLeft baseRight =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash origLeft origRight : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      origLeft.CachedHashesAgree baseLeft ∧ origRight.CachedHashesAgree baseRight
  | _, _ => True

end milhouse.progressive_tree
