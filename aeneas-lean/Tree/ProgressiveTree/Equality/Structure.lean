import Tree.Equality.Structure
import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Equality of spine structure and binary layers, with all caches ignored. -/
def ProgressiveTree.StructuralEq {T : Type} : ProgressiveTree T → ProgressiveTree T → Prop
  | .ProgressiveZero, .ProgressiveZero => True
  | .ProgressiveNode _ left right, .ProgressiveNode _ otherLeft otherRight =>
      left.StructuralEq otherLeft ∧ right.StructuralEq otherRight
  | _, _ => False

theorem ProgressiveTree.StructuralEq.refl {T : Type} (self : ProgressiveTree T) :
    self.StructuralEq self := by
  induction self <;> simp_all [ProgressiveTree.StructuralEq, tree.Tree.StructuralEq.refl]

theorem ProgressiveTree.StructuralEq.elements_eq {T : Type} {self other : ProgressiveTree T}
    (heq : self.StructuralEq other) : self.elements = other.elements := by
  induction self generalizing other <;> cases other <;>
    simp_all [ProgressiveTree.StructuralEq, ProgressiveTree.elements]
  case ProgressiveNode.ProgressiveNode hash left right ih otherHash otherLeft otherRight =>
    rw [tree.Tree.StructuralEq.elements_eq heq.1, ih heq.2]

/-- Structural equality transports the progressive dense-prefix invariant. -/
theorem ProgressiveTree.StructuralEq.dense {T : Type} {self other : ProgressiveTree T}
    {factor : Option Std.Usize} {depth length : Nat}
    (heq : self.StructuralEq other) (hdense : self.Dense factor depth length) :
    other.Dense factor depth length := by
  induction hdense generalizing other with
  | zero depth =>
    cases other <;> simp only [ProgressiveTree.StructuralEq] at heq
    exact .zero factor depth
  | node hash hleft hright hfull ih =>
    cases other <;> simp only [ProgressiveTree.StructuralEq] at heq
    exact .node _ (tree.Tree.StructuralEq.dense heq.1 hleft) (ih heq.2) hfull

/-- Capacity bounds depend only on the spine shape, which structural equality
    preserves. No additional scalar or packing premise is needed. -/
theorem ProgressiveTree.StructuralEq.fits {T : Type} {self other : ProgressiveTree T}
    {factor : Option Std.Usize} {depth : Nat}
    (heq : self.StructuralEq other) (hfits : self.Fits factor depth) :
    other.Fits factor depth := by
  induction self generalizing other depth <;> cases other <;>
    simp_all [ProgressiveTree.StructuralEq, ProgressiveTree.Fits]

end milhouse.progressive_tree
