import Tree.Rebase.Comparisons

open Aeneas Aeneas.Std Result

namespace milhouse_models

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- A completed Arc comparison supplies the pointee call whenever pointer
identity did not bypass it. No equality soundness or global totality is needed. -/
theorem arc_comparisons_of_eq_success {T : Type} (inst : core.cmp.PartialEq T T)
    {left right : T} {equal : Bool}
    (hsuccess : triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq inst left right = ok equal) :
    triomphe.arc.Arc.ptr_eq left right = ok false →
      ∃ answer, inst.eq left right = ok answer := by
  intro hpointer
  rw [triomphe.arc.Arc.eq_of_ptr_eq_false inst hpointer] at hsuccess
  exact ⟨equal, hsuccess⟩

/-- The selected pointee-call law is exactly what the actual Arc comparison
needs to succeed. A shared pointer omits that law altogether. -/
theorem arc_eq_success_iff {T : Type} (inst : core.cmp.PartialEq T T) (left right : T) :
    (∃ equal, triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq inst left right = ok equal) ↔
      (triomphe.arc.Arc.ptr_eq left right = ok false →
        ∃ equal, inst.eq left right = ok equal) := by
  constructor
  · rintro ⟨equal, hsuccess⟩
    exact arc_comparisons_of_eq_success inst hsuccess
  · exact arc_eq_success inst left right

/-- Successful vector comparison entails termination precisely along its
reached `ne` calls. Unequal lengths and calls after the first true result impose
no obligation, including when such omitted calls would fail or diverge. -/
theorem neComparisons_of_vec_eq_success {T U : Type} (inst : core.cmp.PartialEq T U)
    {left : alloc.vec.Vec T} {right : alloc.vec.Vec U} {equal : Bool}
    (hsuccess : vec_eq inst left right = ok equal) :
    left.val.length = right.val.length → NeComparisons inst (left.val.zip right.val) := by
  intro hlength
  unfold vec_eq alloc.vec.partial_eq.PartialEqVec.ne at hsuccess
  simp only [if_pos hlength] at hsuccess
  rw [bind_eq_ok_iff] at hsuccess
  obtain ⟨different, hloop, _⟩ := hsuccess
  exact neComparisons_of_anyM_success hloop

/-- The input-scoped termination law is necessary and sufficient for the
actual vector comparison to return either Boolean answer. -/
theorem vec_eq_success_iff {T U : Type} (inst : core.cmp.PartialEq T U)
    (left : alloc.vec.Vec T) (right : alloc.vec.Vec U) :
    (∃ equal, vec_eq inst left right = ok equal) ↔
      (left.val.length = right.val.length → NeComparisons inst (left.val.zip right.val)) := by
  constructor
  · rintro ⟨equal, hsuccess⟩
    exact neComparisons_of_vec_eq_success inst hsuccess
  · exact vec_eq_success inst left right

end milhouse_models
