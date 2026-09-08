import Tree.Rebase.Steps

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- The cache law needed by rebasing: corresponding nonzero equal node hashes
    identify equal materialized sequences when their lengths agree. The law
    also holds recursively for corresponding children. It imposes no condition
    on zero caches or on hashes of sequences with different lengths. -/
def Tree.CachedHashesAgree {T : Type} : Tree T → Tree T → Prop
  | .Node origHash origLeft origRight, .Node baseHash baseLeft baseRight =>
      ((¬ ∀ byte ∈ origHash.val, byte = 0#u8) → origHash.val = baseHash.val →
        (origLeft.elements ++ origRight.elements).length =
          (baseLeft.elements ++ baseRight.elements).length →
        origLeft.elements ++ origRight.elements = baseLeft.elements ++ baseRight.elements) ∧
      origLeft.CachedHashesAgree baseLeft ∧ origRight.CachedHashesAgree baseRight
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

private theorem allM_zip_eq {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hsound : ∀ x y, eqInst.eq x y = ok true → x = y)
    (orig base : _root_.List T) (hlength : orig.length = base.length)
    (heq : _root_.List.allM (fun (x, y) => eqInst.eq x y)
      (_root_.List.zip orig base) = ok true) : orig = base := by
  induction orig generalizing base with
  | nil =>
    cases base <;> simp_all
  | cons x xs ih =>
    cases base with
    | nil => simp at hlength
    | cons y ys =>
      simp only [_root_.List.length_cons, Nat.add_right_cancel_iff] at hlength
      simp only [_root_.List.zip_cons_cons, _root_.List.allM_cons] at heq
      cases hxy : eqInst.eq x y with
      | fail e => simp [hxy] at heq
      | div => simp [hxy] at heq
      | ok equal =>
        cases equal with
        | false => simp [hxy, pure] at heq
        | true =>
          simp only [hxy, bind_tc_ok, ↓reduceIte] at heq
          exact congrArg₂ _root_.List.cons (hsound x y hxy) (ih ys hlength heq)

/-- A successful positive vector comparison implies exact contents equality
    under positive element-equality soundness. No termination or negative
    comparison law is required. -/
theorem vec_eq_contents {T : Type} (eqInst : core.cmp.PartialEq T T)
    (hsound : ∀ x y, eqInst.eq x y = ok true → x = y)
    {orig base : alloc.vec.Vec T}
    (heq : alloc.vec.partial_eq.PartialEqVec.eq eqInst orig base = ok true) :
    orig.val = base.val := by
  unfold alloc.vec.partial_eq.PartialEqVec.eq at heq
  split at heq
  · exact allM_zip_eq eqInst hsound orig.val base.val (by assumption) heq
  · simp at heq

end milhouse.tree
