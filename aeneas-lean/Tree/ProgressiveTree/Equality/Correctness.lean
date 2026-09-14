import Tree.Equality.Correctness
import Tree.ProgressiveTree.Equality.Scope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem arc_eq_of_eq_spec {T : Type} (ValueInst : Value T)
    (self other : ProgressiveTree T)
    (hcompare : triomphe.arc.Arc.ptr_eq self other = ok false → ∃ equal,
      ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq ValueInst ValueInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq other)) :
    ∃ equal, ProgressiveTree.arc_eq ValueInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq other) := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec self other
  cases same with
  | true =>
    refine ⟨true, ?_, ?_⟩
    · rw [ProgressiveTree.arc_eq]
      simp [hpointer]
    · simp [hsame rfl, ProgressiveTree.StructuralEq.refl]
  | false =>
    simpa only [ProgressiveTree.arc_eq, hpointer, bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using hcompare hpointer

/-- Derived progressive-tree equality terminates and characterizes the
    complete structure, ignoring caches. Element laws concern only selected
    input pairs; a suffix is considered only after its binary layer agrees. -/
theorem ProgressiveTree.partial_eq_spec {T : Type} (ValueInst : Value T)
    (self other : ProgressiveTree T)
    (hne : self.EqualityOn ValueInst.corecmpPartialEqInst
      (milhouse_models.NeSpecAt ValueInst.corecmpPartialEqInst) other) :
    ∃ equal,
      ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq ValueInst ValueInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq other) := by
  induction self generalizing other with
  | ProgressiveZero =>
    cases other with
    | ProgressiveZero =>
      exact ⟨true, by simp only [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq],
        by simp [ProgressiveTree.StructuralEq]⟩
    | ProgressiveNode =>
      exact ⟨false, by simp only [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq],
        by simp [ProgressiveTree.StructuralEq]⟩
  | ProgressiveNode hash left right ih =>
    cases other with
    | ProgressiveZero =>
      exact ⟨false, by simp only [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq],
        by simp [ProgressiveTree.StructuralEq]⟩
    | ProgressiveNode otherHash otherLeft otherRight =>
      obtain ⟨leftEqual, hleft, hleftSame⟩ := tree.Tree.arc_eq_spec ValueInst left otherLeft hne.1
      cases leftEqual with
      | false =>
        refine ⟨false, ?_, ?_⟩
        · rw [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq]
          simp [hleft]
        · simp [ProgressiveTree.StructuralEq, ← hleftSame]
      | true =>
        obtain ⟨rightEqual, hright, hrightSame⟩ := arc_eq_of_eq_spec ValueInst right otherRight
          (fun hpointer => ih otherRight (hne.2 (hleftSame.mp rfl) hpointer))
        refine ⟨rightEqual, ?_, ?_⟩
        · rw [ProgressiveTree.Insts.CoreCmpPartialEqProgressiveTree.eq]
          cases rightEqual <;> simp [hleft, hright]
        · simp [ProgressiveTree.StructuralEq, ← hleftSame, ← hrightSame]

/-- Arc comparison has the same complete structural specification, including
    the pointer shortcut and recursively proved comparison of distinct nodes. -/
theorem ProgressiveTree.arc_eq_spec {T : Type} (ValueInst : Value T)
    (self other : ProgressiveTree T)
    (hne : self.ArcEqualityOn ValueInst.corecmpPartialEqInst
      (milhouse_models.NeSpecAt ValueInst.corecmpPartialEqInst) other) :
    ∃ equal, ProgressiveTree.arc_eq ValueInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq other) :=
  arc_eq_of_eq_spec ValueInst self other
    (fun hpointer => ProgressiveTree.partial_eq_spec ValueInst self other (hne hpointer))

end milhouse.progressive_tree
