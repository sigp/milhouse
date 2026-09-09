import Tree.Rebase.Comparisons
import Tree.ProgressiveTree.Geometry

open Aeneas Aeneas.Std Result
open milhouse.tree

namespace milhouse.progressive_tree

/-- Comparisons selected by the actual progressive layer lengths and binary
depths. The recorded total lengths may differ from stored contents. Pointer
sharing and binary cache shortcuts omit descendant comparison obligations. -/
def ProgressiveTree.RebaseComparisons {T : Type} (inst : core.cmp.PartialEq T T) :
    ProgressiveTree T → ProgressiveTree T → Option Std.Usize → Nat → Nat → Nat → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight,
      factor, packingDepth, origLength, baseLength, depth =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      left.RebaseComparisons inst baseLeft
        (some (min (origLength - progressiveCapacity factor depth) (subtreeCapacity factor (2 * depth)),
          min (baseLength - progressiveCapacity factor depth) (subtreeCapacity factor (2 * depth))))
        (2 * depth + packingDepth) ∧
      right.RebaseComparisons inst baseRight factor packingDepth origLength baseLength (depth + 1)
  | _, _, _, _, _, _, _ => True

/-- Global element termination supplies every selected layer scope. The
actual success specifications use only the weaker metadata-specific scope. -/
theorem ProgressiveTree.rebaseComparisons_of_total {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ left right, ∃ equal, inst.eq left right = ok equal)
    (hne : ∀ left right, ∃ different, inst.ne left right = ok different)
    (orig base : ProgressiveTree T) (factor : Option Std.Usize) (packingDepth origLength baseLength depth : Nat) :
    orig.RebaseComparisons inst base factor packingDepth origLength baseLength depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base <;> simp only [ProgressiveTree.RebaseComparisons]
    exact fun _ => ⟨Tree.rebaseComparisons_of_total inst heq hne _ _ _ _, ih _ _⟩

end milhouse.progressive_tree
