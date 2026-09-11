import Tree.Rebase.Density
import Tree.Arithmetic

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Whether the action also certifies equality with the base. -/
def RebaseAction.IsEqual {A : Type} : RebaseAction A → Prop
  | .EqualNoop | .EqualReplace _ => True
  | .NotEqualNoop | .NotEqualReplace _ => False

/-- The action preserves the original materialized length; an equality action
    additionally certifies that the base has the same length. -/
def RebaseAction.LengthCorrect {T : Type} (orig base : Tree T)
    (action : RebaseAction (Tree T)) : Prop :=
  (applyRebaseAction orig action).elements.length = orig.elements.length ∧
    (action.IsEqual → orig.elements.length = base.elements.length)

theorem combineRebaseActions_length_correct {T : Type}
    (origHash baseHash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T))
    (hleft : leftAction.LengthCorrect origLeft baseLeft)
    (hright : rightAction.LengthCorrect origRight baseRight) :
    (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
      leftAction rightAction).LengthCorrect (.Node origHash origLeft origRight)
        (.Node baseHash baseLeft baseRight) := by
  cases leftAction <;> cases rightAction <;>
    simp_all [RebaseAction.LengthCorrect, RebaseAction.IsEqual, applyRebaseAction,
      combineRebaseActions, Tree.elements]

/-- Successful recursive child rebasing records the actual split-length
    calculation, both recursive calls, and the exact action combination. -/
theorem rebaseChildren_success_state {T : Type} (ValueInst : Value T)
    {origHash baseHash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    {origLeft origRight baseLeft baseRight : Tree T}
    {lengths : Option (utils.Length × utils.Length)} {fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hchildren : rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
      lengths fullDepth = ok (core.result.Result.Ok action)) :
    ∃ newDepth mapped leftLengths rightLengths leftAction rightAction,
      fullDepth - 1#usize = ok newDepth ∧
      core.option.Option.map
        (Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength
          ValueInst) lengths newDepth = ok mapped ∧
      core.option.OptionPair.unzip mapped = ok (leftLengths, rightLengths) ∧
      Tree.rebase_on ValueInst origLeft baseLeft leftLengths newDepth = ok (core.result.Result.Ok leftAction) ∧
      Tree.rebase_on ValueInst origRight baseRight rightLengths newDepth = ok (core.result.Result.Ok rightAction) ∧
      action = combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight leftAction rightAction := by
  unfold rebaseChildren at hchildren
  rw [bind_eq_ok_iff] at hchildren
  obtain ⟨newDepth, hdepth, hchildren⟩ := hchildren
  rw [bind_eq_ok_iff] at hchildren
  obtain ⟨mapped, hmapped, hchildren⟩ := hchildren
  rw [bind_eq_ok_iff] at hchildren
  obtain ⟨⟨leftLengths, rightLengths⟩, hsplit, hchildren⟩ := hchildren
  dsimp! only at hchildren
  rw [bind_eq_ok_iff] at hchildren
  obtain ⟨leftResult, hleftResult, hchildren⟩ := hchildren
  cases leftResult with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at hchildren
  | Ok leftAction =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hchildren
    rw [bind_eq_ok_iff] at hchildren
    obtain ⟨rightResult, hrightResult, hchildren⟩ := hchildren
    cases rightResult with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hchildren
    | Ok rightAction =>
      refine ⟨newDepth, mapped, leftLengths, rightLengths, leftAction, rightAction,
        hdepth, hmapped, hsplit, hleftResult, hrightResult, ?_⟩
      cases leftAction <;> cases rightAction <;>
        simpa [core.result.Result.Insts.CoreOpsTry.branch, combineRebaseActions] using hchildren.symm

/-- The length-splitting callback gives the dense left prefix and remaining
    right suffix at the supplied child capacity. Checked shifts and
    subtraction bounds follow from its successful execution. -/
theorem rebase_split_lengths_spec {T : Type} (ValueInst : Value T)
    {origLength baseLength newDepth origLeft baseLeft origRight baseRight : Std.Usize}
    (hsplit : Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once
      ValueInst newDepth (origLength, baseLength) = ok ((origLeft, baseLeft), (origRight, baseRight))) :
    origLeft.val = min origLength.val (2 ^ newDepth.val) ∧
      baseLeft.val = min baseLength.val (2 ^ newDepth.val) ∧
      origRight.val = origLength.val - 2 ^ newDepth.val ∧
      baseRight.val = baseLength.val - 2 ^ newDepth.val := by
  unfold Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once at hsplit
  dsimp! only at hsplit
  rw [bind_eq_ok_iff] at hsplit
  obtain ⟨capacity, hcapacity, hsplit⟩ := hsplit
  have hcapacityVal := usize_shift_left_one_val hcapacity
  rw [bind_eq_ok_iff] at hsplit
  obtain ⟨leftOrig, hleftOrig, hsplit⟩ := hsplit
  have hleftOrigVal := length_min_val hleftOrig
  simp only [utils.Length.as_usize, bind_tc_ok] at hsplit
  rw [bind_eq_ok_iff] at hsplit
  obtain ⟨rightOrig, hrightOrig, hsplit⟩ := hsplit
  have hrightOrigVal := UScalar.sub_equiv origLength leftOrig
  rw [hrightOrig] at hrightOrigVal
  rw [bind_eq_ok_iff] at hsplit
  obtain ⟨leftBase, hleftBase, hsplit⟩ := hsplit
  have hleftBaseVal := length_min_val hleftBase
  rw [bind_eq_ok_iff] at hsplit
  obtain ⟨rightBase, hrightBase, hsplit⟩ := hsplit
  have hrightBaseVal := UScalar.sub_equiv baseLength leftBase
  rw [hrightBase] at hrightBaseVal
  simp only [ok.injEq, Prod.mk.injEq] at hsplit
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hsplit
  obtain ⟨_, horigSub, _⟩ := hrightOrigVal
  obtain ⟨_, hbaseSub, _⟩ := hrightBaseVal
  refine ⟨by omega, by omega, ?_, ?_⟩ <;> omega

end milhouse.tree
