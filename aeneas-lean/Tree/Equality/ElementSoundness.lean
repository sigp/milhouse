import Tree.Equality.Inputs
import Tree.Arc.Equality

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- False Arc inequality identifies equal values using only the compared
pair's soundness, and only when pointer identity does not supply equality. -/
theorem arc_ne_false_imp_eq_on {T : Type} (inst : core.cmp.PartialEq T T)
    {left right : T}
    (hsound : triomphe.arc.Arc.ptr_eq left right = ok false → NeSoundAt inst left right)
    (heq : triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.ne inst left right = ok false) : left = right := by
  obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec left right
  cases same with
  | true => exact hsame rfl
  | false =>
    rw [triomphe.arc.Arc.ne_of_ptr_eq_false inst hpointer] at heq
    exact hsound hpointer heq

private theorem anyM_ne_false_contents {T : Type} (inst : core.cmp.PartialEq T T)
    (left right : _root_.List T) (hlength : left.length = right.length)
    (hsound : NeOn inst (NeSoundAt inst) (left.zip right))
    (heq : _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) (left.zip right) = ok false) :
    left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons x xs ih =>
    cases right with
    | nil => simp at hlength
    | cons y ys =>
      simp only [_root_.List.length_cons, Nat.add_right_cancel_iff] at hlength
      cases hcall : inst.ne x y with
      | fail error => simp [hcall] at heq
      | div => simp [hcall] at heq
      | ok different =>
        cases different with
        | true => simp [hcall, pure] at heq
        | false =>
          have htail : _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) (xs.zip ys) = ok false := by
            simpa [hcall] using heq
          exact congrArg₂ _root_.List.cons (hsound.1 hcall) (ih ys hlength (hsound.2 hcall) htail)

/-- Positive packed-vector equality needs soundness only on its reached
element calls. Length agreement follows from the actual successful result. -/
theorem vec_ne_false_imp_eq_on {T : Type} (inst : core.cmp.PartialEq T T)
    {left right : alloc.vec.Vec T}
    (hsound : left.val.length = right.val.length →
      NeOn inst (NeSoundAt inst) (left.val.zip right.val))
    (heq : alloc.vec.partial_eq.PartialEqVec.ne inst left right = ok false) : left.val = right.val := by
  unfold alloc.vec.partial_eq.PartialEqVec.ne at heq
  split at heq
  · exact anyM_ne_false_contents inst left.val right.val (by assumption) (hsound (by assumption)) heq
  · simp at heq

end milhouse_models
