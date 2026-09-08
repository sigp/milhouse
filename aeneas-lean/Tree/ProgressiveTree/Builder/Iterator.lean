import Tree.Iterator
import Tree.ProgressiveTree.Builder.Invariant

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Consuming a finite iterator appends its yielded sequence and preserves the
    counter invariant. The premise describes actual `next` calls, rather than
    assuming any property of the builder's result. -/
theorem ProgressiveTreeBuilder.extend_from_iter_elements {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    (self : ProgressiveTreeBuilder T) (iter : I) (values : _root_.List T)
    (hyields : IteratorYields iterInst.next iter values)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements ++ values ∧
      result.length.val = self.length.val + values.length ∧
      (self.Counts → result.Counts) := by
  change ProgressiveTreeBuilder.extend_from_iter_loop ValueInst iterInst iter self =
    ok (core.result.Result.Ok (), result) at hextend
  induction hyields generalizing self with
  | nil hnext =>
    rw [ProgressiveTreeBuilder.extend_from_iter_loop, loop] at hextend
    simp! only [ProgressiveTreeBuilder.extend_from_iter_loop.body, hnext, bind_tc_ok] at hextend
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hextend
    subst result
    simp
  | @cons iter rest value values hnext hyields ih =>
    rw [ProgressiveTreeBuilder.extend_from_iter_loop, loop] at hextend
    simp! only [ProgressiveTreeBuilder.extend_from_iter_loop.body, hnext, bind_tc_ok] at hextend
    cases hpush : ProgressiveTreeBuilder.push ValueInst self value with
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
        obtain ⟨helements, hlength, hcounts⟩ := ih pushed hextend
        obtain ⟨happended, hincrement, _⟩ := ProgressiveTreeBuilder.push_contents ValueInst self value hpush
        refine ⟨?_, ?_, fun h => hcounts (ProgressiveTreeBuilder.push_preserves_counts
          ValueInst self value h hpush)⟩
        · simpa [happended, _root_.List.append_assoc] using helements
        · simpa [hincrement, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength

/-- Successful iterator consumption preserves the full builder invariant.
    The loop proof needs no separate finiteness or iterator-output premise. -/
theorem ProgressiveTreeBuilder.extend_from_iter_preserves_valid {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T) (iter : I)
    (hvalid : self.Valid ValueInst factor) {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result)) :
    result.Valid ValueInst factor := by
  let inv := fun (state : I × ProgressiveTreeBuilder T) => state.2.Valid ValueInst factor
  let post := fun (result : core.result.Result Unit error.Error × ProgressiveTreeBuilder T) =>
    result.1 = core.result.Result.Ok () → result.2.Valid ValueInst factor
  have hbody : ∀ state, inv state → ∀ flow,
      ProgressiveTreeBuilder.extend_from_iter_loop.body ValueInst iterInst state.1 state.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, current⟩ hinv flow hstep
    unfold ProgressiveTreeBuilder.extend_from_iter_loop.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, cursor1⟩, _, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none =>
      simp only [ok.injEq] at hstep
      subst flow
      exact fun _ => hinv
    | some value =>
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
    (fun state => ProgressiveTreeBuilder.extend_from_iter_loop.body ValueInst iterInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (iter, self) hvalid _ (by
      convert hextend using 1
      unfold ProgressiveTreeBuilder.extend_from_iter ProgressiveTreeBuilder.extend_from_iter_loop
      rfl) rfl

end milhouse.progressive_tree
