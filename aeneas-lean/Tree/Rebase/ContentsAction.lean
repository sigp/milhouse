import Tree.Rebase.Steps
import Tree.Rebase.HashShortcut
import Tree.Equality.ElementSoundness

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

/-- A successful positive Rust vector comparison implies exact contents
    equality using false-`ne` soundness only on the reached input pairs.
    Unequal lengths and pairs after the first true `ne` need no law. No element
    `eq`, reflexivity, or comparison termination premise is required. -/
theorem vec_eq_contents {T : Type} (eqInst : core.cmp.PartialEq T T)
    {orig base : alloc.vec.Vec T}
    (hsound : orig.val.length = base.val.length →
      milhouse_models.NeOn eqInst (milhouse_models.NeSoundAt eqInst) (orig.val.zip base.val))
    (heq : milhouse_models.vec_eq eqInst orig base = ok true) :
    orig.val = base.val := by
  unfold milhouse_models.vec_eq at heq
  cases hne : alloc.vec.partial_eq.PartialEqVec.ne eqInst orig base with
  | fail e => simp [hne] at heq
  | div => simp [hne] at heq
  | ok different =>
    cases different with
    | true => simp [hne] at heq
    | false => exact milhouse_models.vec_ne_false_imp_eq_on eqInst hsound hne

end milhouse.tree
