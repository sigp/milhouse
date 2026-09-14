import Tree.ProgressiveList.PopFront.Builder

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The actual successful rebuilding stages of a nonzero front removal. This
    relation records calls and exact final state, not a sequence postcondition. -/
def ProgressiveList.PopFrontRebuild {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (n : Std.Usize) (result : ProgressiveList T U) : Prop :=
  ∃ beforeLength cursor initial built tree length updates,
    ProgressiveList.len ValueInst mapInst self = ok beforeLength ∧ n ≤ beforeLength ∧
    ProgressiveList.iter_from ValueInst mapInst self n = ok (core.result.Result.Ok cursor) ∧
    ProgressiveTreeBuilder.new ValueInst = ok (core.result.Result.Ok initial) ∧
    ProgressiveListIter.extend_builder ValueInst mapInst cursor initial = ok (core.result.Result.Ok (), built) ∧
    ProgressiveTreeBuilder.finish ValueInst built = ok (core.result.Result.Ok (tree, length)) ∧
    mapInst.coredefaultDefaultInst.default = ok updates ∧
    result = { tree, length, updates }

private theorem pop_front_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (n : Std.Usize)
    {status : core.result.Result Unit error.Error} {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (status, result)) :
    match status with
    | .Err _ => result = self
    | .Ok _ => (n = 0#usize ∧ result = self) ∨
      (n ≠ 0#usize ∧ self.PopFrontRebuild ValueInst mapInst n result) := by
  unfold ProgressiveList.pop_front at hpop
  split at hpop
  · rename_i hzero
    simp only [ok.injEq, Prod.mk.injEq] at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    exact Or.inl ⟨hzero, rfl⟩
  · rename_i hnonzero
    rw [bind_eq_ok_iff] at hpop
    obtain ⟨beforeLength, hlength, hpop⟩ := hpop
    split at hpop
    · simp only [ok.injEq, Prod.mk.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      rfl
    · rename_i hinside
      rw [bind_eq_ok_iff] at hpop
      obtain ⟨iterStatus, hiter, hpop⟩ := hpop
      cases iterStatus with
      | Err e =>
        simp! [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpop
        obtain ⟨rfl, rfl⟩ := hpop
        rfl
      | Ok cursor =>
        simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpop
        rw [bind_eq_ok_iff] at hpop
        obtain ⟨newStatus, hnew, hpop⟩ := hpop
        cases newStatus with
        | Err e =>
          simp! [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          rfl
        | Ok initial =>
          simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpop
          rw [bind_eq_ok_iff] at hpop
          obtain ⟨⟨extendStatus, built⟩, hextend, hpop⟩ := hpop
          dsimp! only at hpop
          cases extendStatus with
          | Err e =>
            simp! [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpop
            obtain ⟨rfl, rfl⟩ := hpop
            rfl
          | Ok success =>
            cases success
            simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpop
            rw [bind_eq_ok_iff] at hpop
            obtain ⟨finishStatus, hfinish, hpop⟩ := hpop
            cases finishStatus with
            | Err e =>
              simp! [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpop
              obtain ⟨rfl, rfl⟩ := hpop
              rfl
            | Ok pair =>
              obtain ⟨tree, length⟩ := pair
              simp! only [core.result.Result.Insts.CoreOpsTry.branch,
                triomphe.arc.Arc.new, bind_tc_ok] at hpop
              rw [bind_eq_ok_iff] at hpop
              obtain ⟨updates, hdefault, hpop⟩ := hpop
              simp only [ok.injEq, Prod.mk.injEq] at hpop
              obtain ⟨rfl, rfl⟩ := hpop
              exact Or.inr ⟨hnonzero, beforeLength, cursor, initial, built, tree, length, updates,
                hlength, le_of_not_gt hinside, hiter, hnew, hextend, hfinish, hdefault, rfl⟩

/-- Removing zero elements is an unconditional no-op, including for generic
    maps whose observers or default construction fail. -/
theorem ProgressiveList.pop_front_zero {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U) :
    ProgressiveList.pop_front ValueInst mapInst self 0#usize = ok (core.result.Result.Ok (), self) := by
  simp [ProgressiveList.pop_front]

/-- Oversized removals return the exact bounds error and the unchanged list. -/
theorem ProgressiveList.pop_front_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (n length : Std.Usize)
    (hlength : ProgressiveList.len ValueInst mapInst self = ok length) (hlarge : length < n) :
    ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Err (error.Error.OutOfBoundsIterFrom n length), self) := by
  have hnonzero : n ≠ 0#usize := by scalar_tac
  simp only [ProgressiveList.pop_front, if_neg hnonzero, hlength, bind_tc_ok, if_pos hlarge]

/-- Every returned Rust error preserves the original list, including failures
    from iterator construction, builder initialization, extension, or finish. -/
theorem ProgressiveList.pop_front_error_preserves {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (n : Std.Usize)
    {e : error.Error} {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Err e, result)) :
    result = self :=
  pop_front_state ValueInst mapInst self n hpop

/-- A successful removal is either the zero no-op or exactly the successful
    iterator/builder reconstruction recorded above. -/
theorem ProgressiveList.pop_front_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (n : Std.Usize) {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    (n = 0#usize ∧ result = self) ∨
      (n ≠ 0#usize ∧ self.PopFrontRebuild ValueInst mapInst n result) :=
  pop_front_state ValueInst mapInst self n hpop

end milhouse.progressive_list
