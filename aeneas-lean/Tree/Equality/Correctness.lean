import Tree.Equality.Scope
import Tree.Equality.Comparisons

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem arc_eq_of_eq_spec {T : Type} (ValueInst : Value T) (self other : Tree T)
    (hcompare : triomphe.arc.Arc.ptr_eq self other = ok false →
      ∃ equal, Tree.Insts.CoreCmpPartialEqTree.eq ValueInst ValueInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq other)) :
    ∃ equal, Tree.arc_eq ValueInst self other = ok equal ∧ (equal = true ↔ self.StructuralEq other) := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec self other
  cases same with
  | true =>
    refine ⟨true, ?_, ?_⟩
    · rw [Tree.arc_eq]
      simp [hpointer]
    · simp [hsame rfl, Tree.StructuralEq.refl]
  | false =>
    simpa only [Tree.arc_eq, hpointer, bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using hcompare hpointer

/-- The actual derived binary-tree comparison terminates and characterizes
    structural equality with caches ignored. Element laws apply only to these
    selected input branches; no density, packing, cloning, or hash law is required. -/
theorem Tree.partial_eq_spec {T : Type} (ValueInst : Value T)
    (self other : Tree T)
    (hne : self.EqualityOn ValueInst.corecmpPartialEqInst
      (milhouse_models.NeSpecAt ValueInst.corecmpPartialEqInst) other) :
    ∃ equal, Tree.Insts.CoreCmpPartialEqTree.eq ValueInst ValueInst self other = ok equal ∧
      (equal = true ↔ self.StructuralEq other) := by
  induction self generalizing other with
  | Leaf value =>
    cases other <;> first
    | solve
      | refine ⟨false, ?_, ?_⟩
        · simp only [Tree.Insts.CoreCmpPartialEqTree.eq]
        · simp [Tree.StructuralEq]
    | skip
    rename_i otherValue
    obtain ⟨different, hcompare, hsame⟩ := milhouse_models.arc_ne_spec ValueInst.corecmpPartialEqInst
      value.value otherValue.value hne
    refine ⟨!different, ?_, ?_⟩
    · cases different <;> simp [Tree.Insts.CoreCmpPartialEqTree.eq,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        leaf.Leaf.Insts.CoreCmpPartialEqLeaf.eq, hcompare]
    · cases different <;> simpa [Tree.StructuralEq] using hsame
  | PackedLeaf value =>
    cases other <;> first
    | solve
      | refine ⟨false, ?_, ?_⟩
        · simp only [Tree.Insts.CoreCmpPartialEqTree.eq]
        · simp [Tree.StructuralEq]
    | skip
    rename_i otherValue
    obtain ⟨different, hcompare, hsame⟩ := milhouse_models.vec_ne_spec ValueInst.corecmpPartialEqInst
      value.values otherValue.values hne
    refine ⟨!different, ?_, ?_⟩
    · cases different <;> simp [Tree.Insts.CoreCmpPartialEqTree.eq,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        packed_leaf.PackedLeaf.Insts.CoreCmpPartialEqPackedLeaf.eq, hcompare]
    · cases different <;> simpa [Tree.StructuralEq] using hsame
  | Node hash left right ihLeft ihRight =>
    cases other <;> first
    | solve
      | refine ⟨false, ?_, ?_⟩
        · simp only [Tree.Insts.CoreCmpPartialEqTree.eq]
        · simp [Tree.StructuralEq]
    | skip
    rename_i otherHash otherLeft otherRight
    obtain ⟨leftEqual, hleft, hleftSame⟩ := arc_eq_of_eq_spec ValueInst left otherLeft
      (fun hpointer => ihLeft otherLeft (hne.1 hpointer))
    cases leftEqual with
    | false =>
      refine ⟨false, ?_, ?_⟩
      · rw [Tree.Insts.CoreCmpPartialEqTree.eq]
        simp [hleft]
      · simp [Tree.StructuralEq, ← hleftSame]
    | true =>
      obtain ⟨rightEqual, hright, hrightSame⟩ := arc_eq_of_eq_spec ValueInst right otherRight
        (fun hpointer => ihRight otherRight (hne.2 (hleftSame.mp rfl) hpointer))
      refine ⟨rightEqual, ?_, ?_⟩
      · rw [Tree.Insts.CoreCmpPartialEqTree.eq]
        cases rightEqual <;> simp [hleft, hright]
      · simp [Tree.StructuralEq, ← hleftSame, ← hrightSame]
  | Zero depth =>
    cases other <;> first
    | solve
      | refine ⟨false, ?_, ?_⟩
        · simp only [Tree.Insts.CoreCmpPartialEqTree.eq]
        · simp [Tree.StructuralEq]
    | skip
    rename_i otherDepth
    refine ⟨decide (depth = otherDepth), ?_, by simp [Tree.StructuralEq]⟩
    rw [Tree.Insts.CoreCmpPartialEqTree.eq]
    by_cases heq : depth = otherDepth
    · simp [lift, heq]
    · have hval : depth.val ≠ otherDepth.val := fun h => heq (UScalar.eq_of_val_eq h)
      simp [lift, heq, hval]

/-- Concrete Arc comparison has the same structural specification, including
    its pointer shortcut. The recursive comparison is proved above. -/
theorem Tree.arc_eq_spec {T : Type} (ValueInst : Value T)
    (self other : Tree T)
    (hne : self.ArcEqualityOn ValueInst.corecmpPartialEqInst
      (milhouse_models.NeSpecAt ValueInst.corecmpPartialEqInst) other) :
    ∃ equal, Tree.arc_eq ValueInst self other = ok equal ∧ (equal = true ↔ self.StructuralEq other) :=
  arc_eq_of_eq_spec ValueInst self other
    (fun hpointer => Tree.partial_eq_spec ValueInst self other (hne hpointer))

end milhouse.tree
