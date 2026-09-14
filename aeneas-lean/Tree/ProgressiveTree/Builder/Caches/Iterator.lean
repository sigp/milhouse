import Tree.ProgressiveTree.Builder.Caches

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Successful iterator consumption preserves cleared caches. The proof
follows the actual loop without a finiteness or iterator-output premise. -/
theorem ProgressiveTreeBuilder.extend_from_iter_preserves_cleared_caches {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    (self : ProgressiveTreeBuilder T) (iter : I)
    (hself : self.CachesCleared) {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result)) :
    result.CachesCleared := by
  let inv := fun (state : I × ProgressiveTreeBuilder T) => state.2.CachesCleared
  let post := fun (result : core.result.Result Unit error.Error × ProgressiveTreeBuilder T) =>
    result.1 = core.result.Result.Ok () → result.2.CachesCleared
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
        exact ProgressiveTreeBuilder.push_preserves_cleared_caches ValueInst current value hinv hpush
  exact loop_success_invariant
    (fun state => ProgressiveTreeBuilder.extend_from_iter_loop.body ValueInst iterInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (iter, self) hself _ (by
      convert hextend using 1
      unfold ProgressiveTreeBuilder.extend_from_iter ProgressiveTreeBuilder.extend_from_iter_loop
      rfl) rfl

end milhouse.progressive_tree
