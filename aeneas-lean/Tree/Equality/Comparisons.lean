import Tree.Arc.Equality
import Tree.Equality.Inputs

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- The semantic law used by derived equality: `ne` terminates and is false
    exactly for equal values. No separate `eq` or clone law is needed by the
    derived tree comparisons, which use this operation. -/
def NeSpec {T : Type} (eqInst : core.cmp.PartialEq T T) : Prop :=
  ∀ x y, NeSpecAt eqInst x y

theorem arc_ne_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (x y : T) (hne : triomphe.arc.Arc.ptr_eq x y = ok false → NeSpecAt eqInst x y) :
    ∃ different, triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.ne eqInst x y = ok different ∧
      (different = false ↔ x = y) := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec x y
  cases same with
  | true =>
    exact ⟨false, triomphe.arc.Arc.ne_of_ptr_eq_true eqInst hpointer, by simp [hsame rfl]⟩
  | false =>
    rw [triomphe.arc.Arc.ne_of_ptr_eq_false eqInst hpointer]
    exact hne hpointer

private theorem anyM_zip_ne_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (left right : _root_.List T) (hlength : left.length = right.length)
    (hne : NeOn eqInst (NeSpecAt eqInst) (left.zip right)) :
    ∃ different, _root_.List.anyM (fun (x, y) => eqInst.ne x y) (left.zip right) = ok different ∧
      (different = false ↔ left = right) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact ⟨false, rfl, by simp⟩
    | cons => simp at hlength
  | cons x xs ih =>
    cases right with
    | nil => simp at hlength
    | cons y ys =>
      simp only [_root_.List.length_cons, Nat.add_right_cancel_iff] at hlength
      obtain ⟨different, hcompare, hsame⟩ := hne.1
      cases different with
      | true =>
        have hxy : x ≠ y := by simpa using hsame
        exact ⟨true, by simp [_root_.List.anyM_cons, hcompare, pure], by simp [hxy]⟩
      | false =>
        have hxy : x = y := hsame.mp rfl
        obtain ⟨different, htail, htailSame⟩ := ih ys hlength (hne.2 hcompare)
        refine ⟨different, ?_, ?_⟩
        · simpa [_root_.List.anyM_cons, hcompare] using htail
        · simpa [hxy] using htailSame

/-- External vector inequality compares these sequences under laws only for
    the reached pairs. Distinct-length vectors need no element law. -/
theorem vec_ne_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (left right : alloc.vec.Vec T)
    (hne : left.val.length = right.val.length → NeOn eqInst (NeSpecAt eqInst) (left.val.zip right.val)) :
    ∃ different, alloc.vec.partial_eq.PartialEqVec.ne eqInst left right = ok different ∧
      (different = false ↔ left.val = right.val) := by
  unfold alloc.vec.partial_eq.PartialEqVec.ne
  split
  · exact anyM_zip_ne_spec eqInst left.val right.val (by assumption) (hne (by assumption))
  · rename_i hlength
    have hvalues : left.val ≠ right.val := by
      intro heq
      exact hlength (congrArg _root_.List.length heq)
    exact ⟨true, rfl, by simp [hvalues]⟩

end milhouse_models
