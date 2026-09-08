import Tree.Builder.Contents
import Tree.ProgressiveTree.Builder.Spine

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- Values already accumulated in completed subtrees and the current builder. -/
def ProgressiveTreeBuilder.elements {T : Type} (self : ProgressiveTreeBuilder T) : _root_.List T :=
  self.subtrees.val.flatMap tree.Tree.elements ++ self.current.elements

/-- The two counters describe the current subtree and the complete sequence. -/
def ProgressiveTreeBuilder.Counts {T : Type} (self : ProgressiveTreeBuilder T) : Prop :=
  self.count.val = self.current.elements.length ∧ self.length.val = self.elements.length

theorem ProgressiveTreeBuilder.new_elements {T : Type} (ValueInst : Value T)
    {self : ProgressiveTreeBuilder T}
    (hnew : ProgressiveTreeBuilder.new ValueInst = ok (core.result.Result.Ok self)) :
    self.elements = [] ∧ self.Counts := by
  unfold ProgressiveTreeBuilder.new at hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨depth, _, hnew⟩ := hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨status, hcurrent, hnew⟩ := hnew
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hnew
  | Ok current =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hnew
    rw [bind_eq_ok_iff] at hnew
    obtain ⟨capacity, _, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    simp [ProgressiveTreeBuilder.elements, ProgressiveTreeBuilder.Counts,
      Builder.new_elements ValueInst _ _ hcurrent]

/-- The common suffix of the extracted push, after any full-subtree rollover. -/
private def pushTail {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) (value : T) :
    Result (core.result.Result Unit error.Error × ProgressiveTreeBuilder T) := do
  let (status, current) ← Builder.push ValueInst self.current value
  let flow ← core.result.Result.Insts.CoreOpsTry.branch status
  match flow with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let count ← self.count + 1#usize
    let length ← self.length + 1#usize
    ok (core.result.Result.Ok (), {self with current, count, length})
  | core.ops.control_flow.ControlFlow.Break residual =>
    let status ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame error.Error) residual
    ok (status, {self with current})

private theorem pushTail_spec {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) (value : T) {result : ProgressiveTreeBuilder T}
    (hpush : pushTail ValueInst self value = ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements ++ [value] ∧ result.length.val = self.length.val + 1 ∧
      (self.count.val = self.current.elements.length →
        result.count.val = result.current.elements.length) := by
  unfold pushTail at hpush
  rw [bind_eq_ok_iff] at hpush
  obtain ⟨⟨status, current⟩, hcurrent, hpush⟩ := hpush
  dsimp! only at hpush
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
  | Ok success =>
    cases success
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, bind_eq_ok_iff] at hpush
    obtain ⟨count, hcount, length, hlength, hpush⟩ := hpush
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hpush
    subst result
    have helements := (Builder.push_elements ValueInst _ _ hcurrent).1
    refine ⟨?_, usize_add_val hlength, ?_⟩
    · simp [ProgressiveTreeBuilder.elements, helements, _root_.List.append_assoc]
    · intro hcountCorrect
      simpa [helements, hcountCorrect] using usize_add_val hcount

/-- Successful push appends the supplied value and increments the total length.
    It also preserves agreement of the current-subtree counter with its contents. -/
theorem ProgressiveTreeBuilder.push_contents {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) (value : T) {result : ProgressiveTreeBuilder T}
    (hpush : ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements ++ [value] ∧ result.length.val = self.length.val + 1 ∧
      (self.count.val = self.current.elements.length →
        result.count.val = result.current.elements.length) := by
  unfold ProgressiveTreeBuilder.push at hpush
  split at hpush
  · rw [bind_eq_ok_iff] at hpush
    obtain ⟨depth, _, hpush⟩ := hpush
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨binaryDepth, _, hpush⟩ := hpush
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨status, hnew, hpush⟩ := hpush
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
    | Ok current =>
      simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, core.mem.replace] at hpush
      rw [bind_eq_ok_iff] at hpush
      obtain ⟨status, hfinish, hpush⟩ := hpush
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
      | Ok output =>
        obtain ⟨output, outputDepth, outputLength⟩ := output
        simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨subtrees, hsubtrees, hpush⟩ := hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨capacity, _, hpush⟩ := hpush
        let prepared := {self with subtrees, current, prog_depth := depth, capacity, count := 0#usize}
        change pushTail ValueInst prepared value = ok (core.result.Result.Ok (), result) at hpush
        obtain ⟨helements, hlength, hcount⟩ := pushTail_spec ValueInst prepared value hpush
        have hempty := Builder.new_elements ValueInst _ _ hnew
        have hfinished := Builder.finish_elements ValueInst _ hfinish
        have hprepared : prepared.elements = self.elements := by
          simp [prepared, ProgressiveTreeBuilder.elements, vec_push_values hsubtrees,
            hfinished, hempty]
        refine ⟨helements.trans (congrArg (· ++ [value]) hprepared), hlength, ?_⟩
        intro _
        exact hcount (by simp [prepared, hempty])
  · exact pushTail_spec ValueInst self value hpush

theorem ProgressiveTreeBuilder.push_preserves_counts {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) (value : T) {result : ProgressiveTreeBuilder T}
    (hcounts : self.Counts)
    (hpush : ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result)) :
    result.Counts := by
  obtain ⟨helements, hlength, hcount⟩ := ProgressiveTreeBuilder.push_contents ValueInst self value hpush
  refine ⟨hcount hcounts.1, ?_⟩
  simp [hlength, helements, hcounts.2]

/-- Finalization preserves all accumulated values and the recorded length.
    Counter agreement is needed because Rust skips the current builder when its
    count is zero; no density, packing, cloning, or arithmetic law is needed. -/
theorem ProgressiveTreeBuilder.finish_elements {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) {output : ProgressiveTree T} {length : Std.Usize}
    (hcount : self.count.val = self.current.elements.length)
    (hfinish : ProgressiveTreeBuilder.finish ValueInst self =
      ok (core.result.Result.Ok (output, length))) :
    output.elements = self.elements ∧ length = self.length := by
  unfold ProgressiveTreeBuilder.finish at hfinish
  split at hfinish
  · rw [bind_eq_ok_iff] at hfinish
    obtain ⟨status, hcurrent, hfinish⟩ := hfinish
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hfinish
    | Ok result =>
      obtain ⟨current, depth, currentLength⟩ := result
      simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨subtrees, hsubtrees, hfinish⟩ := hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨assembled, hassemble, hfinish⟩ := hfinish
      simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
      obtain ⟨rfl, rfl⟩ := hfinish
      refine ⟨?_, rfl⟩
      simp [ProgressiveTree.from_spine_subtrees_elements ValueInst _ hassemble,
        ProgressiveTreeBuilder.elements, vec_push_values hsubtrees,
        Builder.finish_elements ValueInst _ hcurrent]
  · rename_i hzero
    rw [bind_eq_ok_iff] at hfinish
    obtain ⟨assembled, hassemble, hfinish⟩ := hfinish
    simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
    obtain ⟨rfl, rfl⟩ := hfinish
    have hempty : self.current.elements = [] := by
      apply _root_.List.length_eq_zero_iff.mp
      have : self.count.val = 0 := by scalar_tac
      omega
    simp [ProgressiveTree.from_spine_subtrees_elements ValueInst _ hassemble,
      ProgressiveTreeBuilder.elements, hempty]

end milhouse.progressive_tree
