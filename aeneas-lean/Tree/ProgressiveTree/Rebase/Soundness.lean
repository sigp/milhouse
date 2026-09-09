import Tree.Rebase.Soundness

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_tree

/-- Rebase equality soundness on corresponding binary layers. Missing suffix
layers require no element law; progressive caches are never compared. -/
def ProgressiveTree.RebaseEqualitySound {T : Type} (inst : core.cmp.PartialEq T T) :
    ProgressiveTree T → ProgressiveTree T → Prop
  | .ProgressiveNode _ left right, .ProgressiveNode _ baseLeft baseRight =>
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
      exact ⟨left.rebaseEqualitySound_of_sound inst heq hne baseLeft, ih baseRight⟩

end milhouse.progressive_tree
