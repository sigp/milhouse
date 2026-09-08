import Tree.ProgressiveList.Iter.Construction
import Tree.ProgressiveTree.Builder.Finish
import Tree.Loop

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful streaming reconstruction appends exactly the cursor's cloned
    sequence and counts it once. Clone identity is required only for the values
    actually yielded, without assumptions about other elements. -/
theorem ProgressiveListIter.extend_builder_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) self values)
    (hclone : ∀ value ∈ values, ValueInst.corecloneCloneInst.clone value = ok value)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result)) :
    result.elements = initial.elements ++ values ∧
      result.length.val = initial.length.val + values.length := by
  change ProgressiveListIter.extend_builder_loop ValueInst mapInst self initial =
    ok (core.result.Result.Ok (), result) at hextend
  induction hyields generalizing initial with
  | nil hnext =>
    rw [ProgressiveListIter.extend_builder_loop, loop] at hextend
    simp! only [ProgressiveListIter.extend_builder_loop.body, hnext, bind_tc_ok] at hextend
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hextend
    subst result
    simp
  | @cons self rest value values hnext hyields ih =>
    rw [ProgressiveListIter.extend_builder_loop, loop] at hextend
    simp! only [ProgressiveListIter.extend_builder_loop.body, hnext,
      hclone value (by simp), bind_tc_ok] at hextend
    cases hpush : ProgressiveTreeBuilder.push ValueInst initial value with
    | fail e => simp [hpush, Bind.bind, Std.bind] at hextend
    | div => simp [hpush, Bind.bind, Std.bind] at hextend
    | ok pair =>
      obtain ⟨status, pushed⟩ := pair
      cases status with
      | Err e =>
        simp! [hpush, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          Bind.bind, Std.bind] at hextend
      | Ok success =>
        cases success
        simp! only [hpush, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at hextend
        obtain ⟨helements, hlength⟩ := ih pushed (fun item hitem => hclone item (by simp [hitem])) hextend
        obtain ⟨happended, hincrement, _⟩ := ProgressiveTreeBuilder.push_contents ValueInst initial value hpush
        constructor
        · simpa [happended, _root_.List.append_assoc] using helements
        · simpa [hincrement, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength

/-- Successful reconstruction preserves the builder's complete invariant,
    independently of iterator finiteness, output values, or clone identity. -/
theorem ProgressiveListIter.extend_builder_preserves_valid {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    {factor : Option Std.Usize} (hvalid : initial.Valid ValueInst factor)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result)) :
    result.Valid ValueInst factor := by
  let inv := fun (state : ProgressiveListIter T U × ProgressiveTreeBuilder T) =>
    state.2.Valid ValueInst factor
  let post := fun (result : core.result.Result Unit error.Error × ProgressiveTreeBuilder T) =>
    result.1 = core.result.Result.Ok () → result.2.Valid ValueInst factor
  have hbody : ∀ state, inv state → ∀ flow,
      ProgressiveListIter.extend_builder_loop.body ValueInst mapInst state.1 state.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, current⟩ hinv flow hstep
    unfold ProgressiveListIter.extend_builder_loop.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, cursor1⟩, _, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none =>
      simp only [ok.injEq] at hstep
      subst flow
      exact fun _ => hinv
    | some entry =>
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨value, _, hstep⟩ := hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨⟨status, pushed⟩, hpush, hstep⟩ := hstep
      dsimp! only at hstep
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
        subst flow
        simp [post]
      | Ok success =>
        cases success
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, ok.injEq] at hstep
        subst flow
        exact ProgressiveTreeBuilder.push_preserves_valid ValueInst hinv value hpush
  exact loop_success_invariant
    (fun state => ProgressiveListIter.extend_builder_loop.body ValueInst mapInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (self, initial) hvalid _ hextend rfl

end milhouse.progressive_list
