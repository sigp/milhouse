import Tree.Equality.Soundness
import Tree.ProgressiveTree.Equality.Structure

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem arc_eq_true_of_eq_sound {T : Type} (ValueInst : Value T)
    {self other : ProgressiveTree T}
    (hsound : ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq
      ValueInst ValueInst self other = ok true → self.StructuralEq other)
    (heq : ProgressiveTree.arc_eq ValueInst self other = ok true) : self.StructuralEq other := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec self other
  cases same with
  | true => simpa only [hsame rfl] using ProgressiveTree.StructuralEq.refl other
  | false =>
    apply hsound
    simpa only [ProgressiveTree.arc_eq, hpointer, bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using heq

/-- A positive progressive comparison is sound even when other comparisons
    may fail or diverge, provided false element inequality is sound. -/
theorem ProgressiveTree.partial_eq_true_imp_structural {T : Type} (ValueInst : Value T)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    {self other : ProgressiveTree T}
    (heq : ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq
      ValueInst ValueInst self other = ok true) : self.StructuralEq other := by
  induction self generalizing other with
  | ProgressiveZero =>
    cases other <;>
      simp_all only [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq,
        ok.injEq, Bool.false_eq_true, ProgressiveTree.StructuralEq]
  | ProgressiveNode hash left right ih =>
    cases other <;> simp only [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq,
      ok.injEq, Bool.false_eq_true] at heq
    rename_i otherHash otherLeft otherRight
    cases hleft : tree.Tree.arc_eq ValueInst left otherLeft <;> simp [hleft] at heq
    rename_i leftEqual
    cases leftEqual <;> simp at heq
    cases hright : ProgressiveTree.arc_eq ValueInst right otherRight <;> simp [hright] at heq
    rename_i rightEqual
    cases rightEqual <;> simp at heq
    exact ⟨tree.Tree.arc_eq_true_imp_structural ValueInst hsound hleft,
      arc_eq_true_of_eq_sound ValueInst ih hright⟩

theorem ProgressiveTree.arc_eq_true_imp_structural {T : Type} (ValueInst : Value T)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    {self other : ProgressiveTree T}
    (heq : ProgressiveTree.arc_eq ValueInst self other = ok true) : self.StructuralEq other :=
  arc_eq_true_of_eq_sound ValueInst (ProgressiveTree.partial_eq_true_imp_structural ValueInst hsound) heq

end milhouse.progressive_tree
