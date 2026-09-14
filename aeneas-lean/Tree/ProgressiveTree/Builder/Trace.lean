import Tree.ProgressiveTree.Builder.Iterator

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Successful iterator extension reflects a finite sequence of actual next
calls through the first none, appends exactly those values, and records the
exact count. No iterator finiteness, packing, or builder invariant is assumed;
the counter invariant is preserved when it held initially. -/
theorem ProgressiveTreeBuilder.extend_from_iter_trace {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    (self : ProgressiveTreeBuilder T) (iter : I) {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result)) :
    ∃ values : _root_.List T, IteratorYields iterInst.next iter values ∧
      result.elements = self.elements ++ values ∧
      result.length.val = self.length.val + values.length ∧
      (self.Counts → result.Counts) := by
  let inv := fun (state : I × ProgressiveTreeBuilder T) =>
    ∀ values, IteratorYields iterInst.next state.1 values →
      ∃ whole, IteratorYields iterInst.next iter whole
  let post := fun (result : core.result.Result Unit error.Error × ProgressiveTreeBuilder T) =>
    result.1 = core.result.Result.Ok () → ∃ values, IteratorYields iterInst.next iter values
  have hbody : ∀ state, inv state → ∀ flow,
      ProgressiveTreeBuilder.extend_from_iter_loop.body ValueInst iterInst state.1 state.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, current⟩ hinv flow hstep
    unfold ProgressiveTreeBuilder.extend_from_iter_loop.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, cursor1⟩, hnext, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none =>
      simp only [ok.injEq] at hstep
      subst flow
      exact fun _ => hinv [] (.nil hnext)
    | some value =>
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨⟨status, pushed⟩, _, hstep⟩ := hstep
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
        intro values htail
        exact hinv (value :: values) (.cons hnext htail)
  have hyields : ∃ values, IteratorYields iterInst.next iter values :=
    loop_success_invariant
      (fun state => ProgressiveTreeBuilder.extend_from_iter_loop.body ValueInst iterInst state.1 state.2)
      inv post (by
        intro state hinv flow hstep
        cases flow with
        | cont next => exact hbody state hinv (.cont next) hstep
        | done result => exact hbody state hinv (.done result) hstep)
      (iter, self) (by intro values hyields; exact ⟨values, hyields⟩)
      _ (by
        convert hextend using 1
        unfold ProgressiveTreeBuilder.extend_from_iter ProgressiveTreeBuilder.extend_from_iter_loop
        rfl) rfl
  obtain ⟨values, hyields⟩ := hyields
  exact ⟨values, hyields, ProgressiveTreeBuilder.extend_from_iter_elements
    ValueInst iterInst self iter values hyields hextend⟩

end milhouse.progressive_tree
