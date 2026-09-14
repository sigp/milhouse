import Tree.Equality.Structure

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Structural equality preserves the entire extracted lookup result,
    including failures and divergence. No packing, density, or bounds laws
    are needed because both trees follow the same computation. -/
theorem Tree.StructuralEq.get_recursive_eq {T : Type} (ValueInst : Value T)
    {self other : Tree T} (heq : self.StructuralEq other)
    (index depth packingDepth : Std.Usize) :
    Tree.get_recursive ValueInst self index depth packingDepth =
      Tree.get_recursive ValueInst other index depth packingDepth := by
  induction self generalizing other index depth packingDepth with
  | Leaf value =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    simp only [Tree.get_recursive, heq]
  | PackedLeaf value =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    rename_i otherValue
    have hvalues : value.values = otherValue.values := alloc.vec.Vec.ext _ _ heq
    simp only [Tree.get_recursive, hvalues]
  | Node hash left right ihLeft ihRight =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    conv_lhs => rw [Tree.get_recursive]
    conv_rhs => rw [Tree.get_recursive]
    simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok,
      ihLeft heq.1, ihRight heq.2]
  | Zero depth =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    simp only [Tree.get_recursive]

end milhouse.tree
