import Tree.Equality.Structure
import Tree.Arc.Equality
import Tree.Rebase.ContentsAction

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem arc_ne_false_imp_eq {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hsound : ∀ x y, eqInst.ne x y = ok false → x = y) {self other : T}
    (heq : triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.ne eqInst self other = ok false) :
    self = other := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec self other
  cases same with
  | true => exact hsame rfl
  | false =>
    rw [triomphe.arc.Arc.ne_of_ptr_eq_false eqInst hpointer] at heq
    exact hsound self other heq

private theorem arc_eq_true_of_eq_sound {T : Type} (ValueInst : Value T) {self other : Tree T}
    (hsound : Tree.Insts.CoreCmpPartialEqTree.eq ValueInst ValueInst self other = ok true →
      self.StructuralEq other)
    (heq : Tree.arc_eq ValueInst self other = ok true) : self.StructuralEq other := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec self other
  cases same with
  | true => simpa only [hsame rfl] using Tree.StructuralEq.refl other
  | false =>
    apply hsound
    simpa only [Tree.arc_eq, hpointer, bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using heq

/-- Successful positive equality needs only soundness of false element
    inequality. Completeness, reflexivity, and termination of comparisons are
    unnecessary when the successful execution is given. -/
theorem Tree.partial_eq_true_imp_structural {T : Type} (ValueInst : Value T)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    {self other : Tree T}
    (heq : Tree.Insts.CoreCmpPartialEqTree.eq ValueInst ValueInst self other = ok true) :
    self.StructuralEq other := by
  induction self generalizing other with
  | Leaf value =>
    cases other <;> simp only [Tree.Insts.CoreCmpPartialEqTree.eq, ok.injEq, Bool.false_eq_true] at heq
    rename_i otherValue
    cases hcompare : triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.ne
        ValueInst.corecmpPartialEqInst value.value otherValue.value <;>
      simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        leaf.Leaf.Insts.CoreCmpPartialEqLeaf.eq, hcompare] at heq
    rename_i different
    cases different <;> simp at heq
    exact arc_ne_false_imp_eq ValueInst.corecmpPartialEqInst hsound hcompare
  | PackedLeaf value =>
    cases other <;> simp only [Tree.Insts.CoreCmpPartialEqTree.eq, ok.injEq, Bool.false_eq_true] at heq
    rename_i otherValue
    cases hcompare : alloc.vec.partial_eq.PartialEqVec.ne
        ValueInst.corecmpPartialEqInst value.values otherValue.values <;>
      simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        packed_leaf.PackedLeaf.Insts.CoreCmpPartialEqPackedLeaf.eq, hcompare] at heq
    rename_i different
    cases different <;> simp at heq
    exact vec_eq_contents ValueInst.corecmpPartialEqInst hsound (by simp [milhouse_models.vec_eq, hcompare])
  | Node hash left right ihLeft ihRight =>
    cases other <;> simp only [Tree.Insts.CoreCmpPartialEqTree.eq, ok.injEq, Bool.false_eq_true] at heq
    rename_i otherHash otherLeft otherRight
    cases hleft : Tree.arc_eq ValueInst left otherLeft <;> simp [hleft] at heq
    rename_i leftEqual
    cases leftEqual <;> simp at heq
    cases hright : Tree.arc_eq ValueInst right otherRight <;> simp [hright] at heq
    rename_i rightEqual
    cases rightEqual <;> simp at heq
    exact ⟨arc_eq_true_of_eq_sound ValueInst ihLeft hleft,
      arc_eq_true_of_eq_sound ValueInst ihRight hright⟩
  | Zero depth =>
    cases other <;> simp only [Tree.Insts.CoreCmpPartialEqTree.eq, ok.injEq, Bool.false_eq_true] at heq
    rename_i otherDepth
    apply UScalar.eq_of_val_eq
    simpa [lift] using heq

theorem Tree.arc_eq_true_imp_structural {T : Type} (ValueInst : Value T)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    {self other : Tree T} (heq : Tree.arc_eq ValueInst self other = ok true) :
    self.StructuralEq other :=
  arc_eq_true_of_eq_sound ValueInst (Tree.partial_eq_true_imp_structural ValueInst hsound) heq

end milhouse.tree
