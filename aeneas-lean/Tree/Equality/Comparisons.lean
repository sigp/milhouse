import Tree.Arc.Equality

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- The semantic law used by derived equality: `ne` terminates and is false
    exactly for equal values. No separate `eq` or clone law is needed by the
    derived tree comparisons, which use this operation. -/
def NeSpec {T : Type} (eqInst : core.cmp.PartialEq T T) : Prop :=
  ∀ x y, ∃ different, eqInst.ne x y = ok different ∧ (different = false ↔ x = y)

theorem arc_ne_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hne : NeSpec eqInst) (x y : T) :
    ∃ different, triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.ne eqInst x y = ok different ∧
      (different = false ↔ x = y) := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec x y
  cases same with
  | true =>
    exact ⟨false, triomphe.arc.Arc.ne_of_ptr_eq_true eqInst hpointer, by simp [hsame rfl]⟩
  | false =>
    rw [triomphe.arc.Arc.ne_of_ptr_eq_false eqInst hpointer]
    exact hne x y

private theorem anyM_zip_ne_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hne : NeSpec eqInst) (left right : _root_.List T) (hlength : left.length = right.length) :
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
      obtain ⟨different, hcompare, hsame⟩ := hne x y
      cases different with
      | true =>
        have hxy : x ≠ y := by simpa using hsame
        exact ⟨true, by simp [_root_.List.anyM_cons, hcompare, pure], by simp [hxy]⟩
      | false =>
        have hxy : x = y := hsame.mp rfl
        obtain ⟨different, htail, htailSame⟩ := ih ys hlength
        refine ⟨different, ?_, ?_⟩
        · simpa [_root_.List.anyM_cons, hcompare] using htail
        · simpa [hxy] using htailSame

/-- The external vector inequality model compares complete sequences under
    the element `ne` law, including distinct-length vectors. -/
theorem vec_ne_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hne : NeSpec eqInst) (left right : alloc.vec.Vec T) :
    ∃ different, alloc.vec.partial_eq.PartialEqVec.ne eqInst left right = ok different ∧
      (different = false ↔ left.val = right.val) := by
  unfold alloc.vec.partial_eq.PartialEqVec.ne
  split
  · exact anyM_zip_ne_spec eqInst hne left.val right.val (by assumption)
  · rename_i hlength
    have hvalues : left.val ≠ right.val := by
      intro heq
      exact hlength (congrArg _root_.List.length heq)
    exact ⟨true, rfl, by simp [hvalues]⟩

end milhouse_models
