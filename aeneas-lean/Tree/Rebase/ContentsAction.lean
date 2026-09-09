import Tree.Rebase.Steps
import Tree.Rebase.HashShortcut

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Cache agreement is needed only at a reached nonzero, equal-hash,
equal-length shortcut. Pointer sharing needs no cache law; a hash shortcut
omits all descendant obligations. -/
def Tree.CachedHashesAgree {T : Type} : Tree T → Tree T → Prop
  | .Node origHash origLeft origRight, .Node baseHash baseLeft baseRight =>
      triomphe.arc.Arc.ptr_eq (.Node origHash origLeft origRight : Tree T)
        (.Node baseHash baseLeft baseRight) = ok false →
      (RebaseHashShortcut origHash baseHash
        (origLeft.elements ++ origRight.elements).length
        (baseLeft.elements ++ baseRight.elements).length →
        origLeft.elements ++ origRight.elements = baseLeft.elements ++ baseRight.elements) ∧
      (¬ RebaseHashShortcut origHash baseHash
        (origLeft.elements ++ origRight.elements).length
        (baseLeft.elements ++ baseRight.elements).length →
        origLeft.CachedHashesAgree baseLeft ∧ origRight.CachedHashesAgree baseRight)
  | _, _ => True

/-- Applying an action preserves the original sequence; an equality action
    additionally certifies that the original and base sequences agree. -/
def RebaseAction.ContentsCorrect {T : Type} (orig base : Tree T)
    (action : RebaseAction (Tree T)) : Prop :=
  (applyRebaseAction orig action).elements = orig.elements ∧
    (action.IsEqual → orig.elements = base.elements)

theorem RebaseAction.ContentsCorrect.length_correct {T : Type} {orig base : Tree T}
    {action : RebaseAction (Tree T)} (hcontents : action.ContentsCorrect orig base) :
    action.LengthCorrect orig base :=
  ⟨congrArg _root_.List.length hcontents.1, fun hequal =>
    congrArg _root_.List.length (hcontents.2 hequal)⟩

theorem combineRebaseActions_contents_correct {T : Type}
    (origHash baseHash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T))
    (hleft : leftAction.ContentsCorrect origLeft baseLeft)
    (hright : rightAction.ContentsCorrect origRight baseRight) :
    (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
      leftAction rightAction).ContentsCorrect (.Node origHash origLeft origRight)
        (.Node baseHash baseLeft baseRight) := by
  cases leftAction <;> cases rightAction <;>
    simp_all [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction,
      combineRebaseActions, Tree.elements]

private theorem anyM_zip_ne_false_eq {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hsound : ∀ x y, eqInst.ne x y = ok false → x = y)
    (orig base : _root_.List T) (hlength : orig.length = base.length)
    (heq : _root_.List.anyM (fun (x, y) => eqInst.ne x y)
      (_root_.List.zip orig base) = ok false) : orig = base := by
  induction orig generalizing base with
  | nil =>
    cases base <;> simp_all
  | cons x xs ih =>
    cases base with
    | nil => simp at hlength
    | cons y ys =>
      simp only [_root_.List.length_cons, Nat.add_right_cancel_iff] at hlength
      simp only [_root_.List.zip_cons_cons, _root_.List.anyM_cons] at heq
      cases hxy : eqInst.ne x y with
      | fail e => simp [hxy] at heq
      | div => simp [hxy] at heq
      | ok equal =>
        cases equal with
        | true => simp [hxy, pure] at heq
        | false =>
          simp only [hxy, bind_tc_ok, ↓reduceIte] at heq
          exact congrArg₂ _root_.List.cons (hsound x y hxy) (ih ys hlength heq)

/-- A successful positive Rust vector comparison implies exact contents
    equality when a false element `ne` identifies equal values. Rust's generic
    slice loop uses `ne`; no element `eq`, reflexivity, or termination law is
    required by this successful-execution result. -/
theorem vec_eq_contents {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hsound : ∀ x y, eqInst.ne x y = ok false → x = y)
    {orig base : alloc.vec.Vec T}
    (heq : milhouse_models.vec_eq eqInst orig base = ok true) :
    orig.val = base.val := by
  unfold milhouse_models.vec_eq at heq
  cases hne : alloc.vec.partial_eq.PartialEqVec.ne eqInst orig base with
  | fail e => simp [hne] at heq
  | div => simp [hne] at heq
  | ok different =>
    cases different with
    | true => simp [hne] at heq
    | false =>
      unfold alloc.vec.partial_eq.PartialEqVec.ne at hne
      split at hne
      · exact anyM_zip_ne_false_eq eqInst hsound orig.val base.val (by assumption) hne
      · simp at hne

end milhouse.tree
