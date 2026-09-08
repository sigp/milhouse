import Tree.Equality.Lookup
import Tree.ProgressiveTree.Equality.Structure

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Equal spine structure follows exactly the same extracted routing and
    binary lookup, independently of layout and capacity validity. -/
theorem ProgressiveTree.StructuralEq.get_recursive_eq {T : Type} (ValueInst : Value T)
    {self other : ProgressiveTree T} (heq : self.StructuralEq other)
    (index : Std.Usize) (depth : Std.U32) :
    ProgressiveTree.get_recursive ValueInst self index depth =
      ProgressiveTree.get_recursive ValueInst other index depth := by
  induction self generalizing other index depth with
  | ProgressiveZero =>
    cases other <;> simp only [ProgressiveTree.StructuralEq] at heq
    simp only [ProgressiveTree.get_recursive]
  | ProgressiveNode hash left right ih =>
    cases other <;> simp only [ProgressiveTree.StructuralEq] at heq
    conv_lhs => rw [ProgressiveTree.get_recursive]
    conv_rhs => rw [ProgressiveTree.get_recursive]
    simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok,
      tree.Tree.StructuralEq.get_recursive_eq ValueInst heq.1, ih heq.2]

end milhouse.progressive_tree
