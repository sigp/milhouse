import Tree.Funs

open Aeneas Aeneas.Std Result

namespace triomphe.arc.Arc

/-- A positive pointer-identity result identifies the retained pointees using
the existing pointer model contract, without any element comparison law. -/
theorem eq_of_ptr_eq {T : Type} {left right : T}
    (hpointer : ptr_eq left right = ok true) : left = right := by
  obtain ⟨same, hcall, htrue⟩ := ptr_eq_spec left right
  apply htrue
  simpa only [hpointer, ok.injEq] using hcall.symm

/-- Identical pointers compare equal without invoking the pointee comparison,
    including when that comparison is nonreflexive or cannot return normally. -/
theorem eq_of_ptr_eq_true {T : Type} (eqInst : core.cmp.PartialEq T T)
    {x y : T} (hpointer : ptr_eq x y = ok true) :
    Insts.CoreCmpPartialEqArc.eq eqInst x y = ok true := by
  simp [Insts.CoreCmpPartialEqArc.eq, hpointer]

theorem ne_of_ptr_eq_true {T : Type} (eqInst : core.cmp.PartialEq T T)
    {x y : T} (hpointer : ptr_eq x y = ok true) :
    Insts.CoreCmpPartialEqArc.ne eqInst x y = ok false := by
  simp [Insts.CoreCmpPartialEqArc.ne, hpointer]

/-- Distinct pointers delegate exactly to the generic comparison, preserving
    both its value and any failure or divergence. -/
theorem eq_of_ptr_eq_false {T : Type} (eqInst : core.cmp.PartialEq T T)
    {x y : T} (hpointer : ptr_eq x y = ok false) :
    Insts.CoreCmpPartialEqArc.eq eqInst x y = eqInst.eq x y := by
  simp [Insts.CoreCmpPartialEqArc.eq, hpointer]

theorem ne_of_ptr_eq_false {T : Type} (eqInst : core.cmp.PartialEq T T)
    {x y : T} (hpointer : ptr_eq x y = ok false) :
    Insts.CoreCmpPartialEqArc.ne eqInst x y = eqInst.ne x y := by
  simp [Insts.CoreCmpPartialEqArc.ne, hpointer]

/-- A positive Arc comparison identifies equal values when positive pointee
    comparisons are sound. Pointer identity supplies equality on the shortcut
    path; no pointee reflexivity or termination premise is needed. -/
theorem eq_true_imp_eq {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hsound : ∀ x y, eqInst.eq x y = ok true → x = y)
    {x y : T} (heq : Insts.CoreCmpPartialEqArc.eq eqInst x y = ok true) : x = y := by
  obtain ⟨same, hpointer, hsame⟩ := ptr_eq_spec x y
  cases same with
  | true => exact hsame rfl
  | false =>
    rw [eq_of_ptr_eq_false eqInst hpointer] at heq
    exact hsound x y heq

end triomphe.arc.Arc
