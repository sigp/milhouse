import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- Successful carry merging preserves the entire pending sequence and then
    increments the builder length once. The loop may perform any number of
    merges; no density, counter, or packing invariant is required. -/
theorem Builder.push_loop0_elements {T : Type} (ValueInst : Value T)
    (iter : core.ops.range.Range Std.U32)
    (stack : alloc.vec.Vec (utils.MaybeArced (tree.Tree T)))
    (length : utils.Length) (top : tree.Tree T)
    {resultStack : alloc.vec.Vec (utils.MaybeArced (tree.Tree T))} {resultLength : utils.Length}
    (hloop : Builder.push_loop0 ValueInst iter stack length top =
      ok (core.result.Result.Ok (), resultStack, resultLength)) :
    stackElements resultStack.val = stackElements stack.val ++ top.elements ∧
      resultLength.val = length.val + 1 := by
  let inv := fun (state : core.ops.range.Range Std.U32 ×
      alloc.vec.Vec (utils.MaybeArced (tree.Tree T)) × tree.Tree T) =>
    stackElements state.2.1.val ++ state.2.2.elements = stackElements stack.val ++ top.elements
  let post := fun (result : core.result.Result Unit error.Error ×
      alloc.vec.Vec (utils.MaybeArced (tree.Tree T)) × utils.Length) =>
    result.1 = core.result.Result.Ok () →
      stackElements result.2.1.val = stackElements stack.val ++ top.elements ∧
        result.2.2.val = length.val + 1
  have hbody : ∀ state, inv state → ∀ flow,
      Builder.push_loop0.body ValueInst length state.1 state.2.1 state.2.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, forest, current⟩ hinv flow hstep
    unfold Builder.push_loop0.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨next, cursor1⟩, _, hstep⟩ := hstep
    cases next with
    | none =>
      dsimp! only at hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨forest1, hpush, hstep⟩ := hstep
      simp! only [utils.Length.as_mut, bind_tc_ok, bind_eq_ok_iff] at hstep
      obtain ⟨length1, hlength, hstep⟩ := hstep
      simp only [ok.injEq] at hstep
      subst flow
      intro _
      refine ⟨?_, usize_add_val hlength⟩
      change stackElements forest1.val = _
      rw [vec_push_values hpush, stackElements_append, stackElements_singleton]
      exact hinv
    | some next =>
      dsimp! only at hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨⟨entry, forest1⟩, hpop, hstep⟩ := hstep
      dsimp! only at hstep
      cases entry with
      | none =>
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
        subst flow
        simp [post]
      | some entry =>
        simp! only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok, maybeArced_arced, triomphe.arc.Arc.new] at hstep
        rw [bind_eq_ok_iff] at hstep
        obtain ⟨merged, hnode, hstep⟩ := hstep
        simp only [ok.injEq] at hstep
        subst flow
        change stackElements forest1.val ++ merged.elements = _
        rw [node_unboxed_elements ValueInst hnode]
        change stackElements forest.val ++ current.elements = _ at hinv
        rw [vec_pop_some_values hpop, stackElements_append, stackElements_singleton] at hinv
        simpa [_root_.List.append_assoc] using hinv
  exact loop_success_invariant
    (fun state => Builder.push_loop0.body ValueInst length state.1 state.2.1 state.2.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (iter, stack, top) rfl _ (by
      convert hloop using 1
      unfold Builder.push_loop0
      rfl) rfl

end milhouse.builder
