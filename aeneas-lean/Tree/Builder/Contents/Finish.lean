import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

private abbrev FinishResult (T : Type) :=
  core.result.Result Unit error.Error × alloc.vec.Vec (utils.MaybeArced (tree.Tree T)) ×
    Std.Usize × Std.Usize × utils.Length × Option Std.Usize × Std.Usize × Std.Usize

/-- The common merge branch in the two extracted finishing loops. This is a
    proof abbreviation of the generated expression, including both errors. -/
private def mergeStackStep {T : Type} (ValueInst : Value T)
    (rightError leftError : error.Error) (self : Builder T) (index : Std.Usize) :
    Result (ControlFlow (Builder T × Std.Usize) (FinishResult T)) := do
  let (right, rest) ← alloc.vec.Vec.pop Global self.stack
  let status ← core.option.Option.ok_or right rightError
  let flow ← core.result.Result.Insts.CoreOpsTry.branch status
  match flow with
  | .Continue right =>
    let (left, base) ← alloc.vec.Vec.pop Global rest
    let status ← core.option.Option.ok_or left leftError
    let flow ← core.result.Result.Insts.CoreOpsTry.branch status
    match flow with
    | .Continue left =>
      let left ← utils.MaybeArced.arced left
      let right ← utils.MaybeArced.arced right
      let merged ← tree.Tree.node_unboxed ValueInst left right
      let stack ← alloc.vec.Vec.push base (.Unarced merged)
      let next ← index + 1#usize
      ok (.cont ({ self with stack }, next))
    | .Break residual =>
      let status ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame error.Error) residual
      ok (.done (status, base, self.depth, self.level, self.length,
        self.packing_factor, self.packing_depth, self.capacity))
  | .Break residual =>
    let status ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame error.Error) residual
    ok (.done (status, rest, self.depth, self.level, self.length,
      self.packing_factor, self.packing_depth, self.capacity))

private def stepPreserves {T : Type} (self : Builder T)
    (flow : ControlFlow (Builder T × Std.Usize) (FinishResult T)) : Prop :=
  match flow with
  | .cont next => next.1.elements = self.elements
  | .done result => result.1 = core.result.Result.Ok () →
      stackElements result.2.1.val = self.elements

private theorem mergeStackStep_preserves {T : Type} (ValueInst : Value T)
    (rightError leftError : error.Error) (self : Builder T) (index : Std.Usize)
    {flow : ControlFlow (Builder T × Std.Usize) (FinishResult T)}
    (hstep : mergeStackStep ValueInst rightError leftError self index = ok flow) :
    stepPreserves self flow := by
  unfold mergeStackStep at hstep
  rw [bind_eq_ok_iff] at hstep
  obtain ⟨⟨right, rest⟩, hright, hstep⟩ := hstep
  dsimp! only at hstep
  cases right with
  | none =>
    simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
    subst flow
    simp [stepPreserves]
  | some right =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok] at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨left, base⟩, hleft, hstep⟩ := hstep
    dsimp! only at hstep
    cases left with
    | none =>
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
      subst flow
      simp [stepPreserves]
    | some left =>
      simp only [maybeArced_arced, bind_tc_ok] at hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨merged, hnode, hstep⟩ := hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨stack, hpush, hstep⟩ := hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨next, _, hstep⟩ := hstep
      simp only [ok.injEq] at hstep
      subst flow
      change stackElements stack.val = stackElements self.stack.val
      rw [vec_push_values hpush, vec_pop_some_values hright, vec_pop_some_values hleft]
      simp only [stackElements_append, stackElements_singleton, maybeArcedTree,
        node_unboxed_elements ValueInst hnode, _root_.List.append_assoc]

private theorem finish_packed_body_preserves {T : Type} (ValueInst : Value T)
    (self : Builder T) (nextIndex index : Std.Usize)
    {flow : ControlFlow (Builder T × Std.Usize) (FinishResult T)}
    (hstep : Builder.finish_packed_leaf_loop.body ValueInst nextIndex self index = ok flow) :
    stepPreserves self flow := by
  unfold Builder.finish_packed_leaf_loop.body at hstep
  split at hstep
  · rw [bind_eq_ok_iff] at hstep
    obtain ⟨shift, _, hstep⟩ := hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨shifted, _, hstep⟩ := hstep
    simp only [lift, bind_tc_ok] at hstep
    split at hstep
    · exact mergeStackStep_preserves ValueInst error.Error.BuilderStackEmptyMergeRight
        error.Error.BuilderStackEmptyMergeLeft self index hstep
    · simp only [ok.injEq] at hstep
      subst flow
      exact fun _ => rfl
  · simp only [ok.injEq] at hstep
    subst flow
    exact fun _ => rfl

private theorem finish_level_body_preserves {T : Type} (ValueInst : Value T)
    (self : Builder T) (nextIndex index : Std.Usize)
    {flow : ControlFlow (Builder T × Std.Usize) (FinishResult T)}
    (hstep : Builder.finish_level_loop.body ValueInst nextIndex self index = ok flow) :
    stepPreserves self flow := by
  unfold Builder.finish_level_loop.body at hstep
  split at hstep
  · rw [bind_eq_ok_iff] at hstep
    obtain ⟨shiftedLeft, _, hstep⟩ := hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨shift, _, hstep⟩ := hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨shifted, _, hstep⟩ := hstep
    simp only [lift, bind_tc_ok] at hstep
    split at hstep
    · exact mergeStackStep_preserves ValueInst error.Error.BuilderStackEmptyFinishRight
        error.Error.BuilderStackEmptyFinishLeft self index hstep
    · simp only [ok.injEq] at hstep
      subst flow
      exact fun _ => rfl
  · simp only [ok.injEq] at hstep
    subst flow
    exact fun _ => rfl

private theorem finish_loop_preserves {T : Type}
    (body : Builder T × Std.Usize → Result (ControlFlow (Builder T × Std.Usize) (FinishResult T)))
    (hbody : ∀ state flow, body state = ok flow → stepPreserves state.1 flow)
    (self : Builder T) (index : Std.Usize) {result : FinishResult T}
    (hloop : loop body (self, index) = ok result) (hok : result.1 = core.result.Result.Ok ()) :
    stackElements result.2.1.val = self.elements := by
  apply loop_success_invariant body (fun state => state.1.elements = self.elements)
    (fun result => result.1 = core.result.Result.Ok () →
      stackElements result.2.1.val = self.elements) ?_ (self, index) rfl result hloop hok
  intro state hinv flow hstep
  have hpreserves := hbody state flow hstep
  cases flow with
  | cont next => exact hpreserves.trans hinv
  | done result => exact fun hstatus => (hpreserves hstatus).trans hinv

/-- Finishing a partial packed leaf only merges existing trees and preserves
    the builder's complete value sequence on success. -/
theorem Builder.finish_packed_leaf_elements {T : Type} (ValueInst : Value T)
    (self : Builder T) (nextIndex : Std.Usize) {result : Builder T}
    (hfinish : Builder.finish_packed_leaf ValueInst self nextIndex =
      ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements := by
  unfold Builder.finish_packed_leaf at hfinish
  rw [bind_eq_ok_iff] at hfinish
  obtain ⟨⟨status, stack, depth, level, length, factor, packingDepth, capacity⟩, hloop, hfinish⟩ := hfinish
  simp! only [ok.injEq, Prod.mk.injEq] at hfinish
  obtain ⟨rfl, hresult⟩ := hfinish
  subst result
  exact finish_loop_preserves _
    (fun state flow hstep => finish_packed_body_preserves ValueInst state.1 nextIndex state.2 hstep)
    self 0#usize hloop rfl

/-- Finishing one level preserves the complete value sequence on success,
    without assumptions on the loop counters or initial forest. -/
theorem Builder.finish_level_elements {T : Type} (ValueInst : Value T)
    (self : Builder T) (nextIndex depth : Std.Usize) {result : Builder T}
    (hfinish : Builder.finish_level ValueInst self nextIndex depth =
      ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements := by
  unfold Builder.finish_level at hfinish
  rw [bind_eq_ok_iff] at hfinish
  obtain ⟨index, _, hfinish⟩ := hfinish
  rw [bind_eq_ok_iff] at hfinish
  obtain ⟨⟨status, stack, depth, level, length, factor, packingDepth, capacity⟩, hloop, hfinish⟩ := hfinish
  simp! only [ok.injEq, Prod.mk.injEq] at hfinish
  obtain ⟨rfl, hresult⟩ := hfinish
  subst result
  exact finish_loop_preserves _
    (fun state flow hstep => finish_level_body_preserves ValueInst state.1 nextIndex state.2 hstep)
    self index hloop rfl

private theorem finish_tree_body_preserves {T : Type} (ValueInst : Value T)
    (self : Builder T) (nextIndex : Std.Usize)
    {flow : ControlFlow (Builder T × Std.Usize) (core.result.Result Unit error.Error × Builder T)}
    (hstep : Builder.finish_tree_loop.body ValueInst self nextIndex = ok flow) :
    match flow with
    | .cont next => next.1.elements = self.elements
    | .done result => result.1 = core.result.Result.Ok () → result.2.elements = self.elements := by
  unfold Builder.finish_tree_loop.body at hstep
  rw [bind_eq_ok_iff] at hstep
  obtain ⟨shifted, _, hstep⟩ := hstep
  split at hstep
  · rw [bind_eq_ok_iff] at hstep
    obtain ⟨zeros, _, hstep⟩ := hstep
    simp only [lift, bind_tc_ok] at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, base⟩, hpop, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none =>
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
      subst flow
      simp
    | some entry =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        bind_tc_ok, maybeArced_arced, tree.Tree.zero, triomphe.arc.Arc.new] at hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨padded, hnode, hstep⟩ := hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨stack, hpush, hstep⟩ := hstep
      have hpadding : ({ self with stack } : Builder T).elements = self.elements := by
        unfold Builder.elements
        rw [vec_push_values hpush, vec_pop_some_values hpop]
        simp only [stackElements_append, stackElements_singleton, maybeArcedTree,
          node_unboxed_elements ValueInst hnode, tree.Tree.elements, _root_.List.append_nil]
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨⟨status, merged⟩, hlevel, hstep⟩ := hstep
      dsimp! only at hstep
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
        subst flow
        simp
      | Ok success =>
        cases success
        have hmerged := Builder.finish_level_elements ValueInst _ _ _ hlevel
        simp only [bind_tc_ok] at hstep
        simp only [bind_eq_ok_iff] at hstep
        obtain ⟨sum, _, difference, _, power, _, next, _, hstep⟩ := hstep
        simp only [ok.injEq] at hstep
        subst flow
        exact hmerged.trans hpadding
  · simp only [ok.injEq] at hstep
    subst flow
    exact fun _ => rfl

/-- Padding with zero subtrees and merging up the tree preserve the complete
    pending sequence. This successful-execution theorem needs no builder
    invariant, arithmetic bound, or termination premise. -/
theorem Builder.finish_tree_elements {T : Type} (ValueInst : Value T)
    (self : Builder T) (nextIndex : Std.Usize) {result : Builder T}
    (hfinish : Builder.finish_tree ValueInst self nextIndex =
      ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements := by
  apply loop_success_invariant
    (fun (state : Builder T × Std.Usize) => Builder.finish_tree_loop.body ValueInst state.1 state.2)
    (fun state => state.1.elements = self.elements)
    (fun result => result.1 = core.result.Result.Ok () → result.2.elements = self.elements)
    ?_ (self, nextIndex) rfl (core.result.Result.Ok (), result) hfinish rfl
  intro state hinv flow hstep
  have hpreserves := finish_tree_body_preserves ValueInst state.1 state.2 hstep
  cases flow with
  | cont next => exact hpreserves.trans hinv
  | done result => exact fun hstatus => (hpreserves hstatus).trans hinv

/-- Common finalization suffix of `Builder.finish`, kept as an exact proof
    abbreviation of the generated expression. -/
private def finishTail {T : Type} (ValueInst : Value T) (self : Builder T) (nextIndex : Std.Usize) :
    Result (core.result.Result (tree.Tree T × Std.Usize × utils.Length) error.Error) := do
  let (status, finished) ← Builder.finish_tree ValueInst self nextIndex
  let flow ← core.result.Result.Insts.CoreOpsTry.branch status
  match flow with
  | .Continue _ =>
    let (entry, rest) ← alloc.vec.Vec.pop Global finished.stack
    let status ← core.option.Option.ok_or entry error.Error.BuilderStackEmptyFinalize
    let flow ← core.result.Result.Insts.CoreOpsTry.branch status
    match flow with
    | .Continue entry =>
      let tree ← utils.MaybeArced.arced entry
      let empty ← alloc.vec.Vec.is_empty Global rest
      if empty then ok (.Ok (tree, finished.depth, finished.length))
      else ok (.Err error.Error.BuilderStackLeftover)
    | .Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (tree.Tree T × Std.Usize × utils.Length) (core.convert.FromSame error.Error) residual
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (tree.Tree T × Std.Usize × utils.Length) (core.convert.FromSame error.Error) residual

private theorem finishTail_elements {T : Type} (ValueInst : Value T) (self : Builder T)
    (nextIndex : Std.Usize) {output : tree.Tree T} {depth : Std.Usize} {length : utils.Length}
    (hfinish : finishTail ValueInst self nextIndex = ok (core.result.Result.Ok (output, depth, length))) :
    output.elements = self.elements := by
  unfold finishTail at hfinish
  rw [bind_eq_ok_iff] at hfinish
  obtain ⟨⟨status, finished⟩, htree, hfinish⟩ := hfinish
  dsimp! only at hfinish
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hfinish
  | Ok success =>
    cases success
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hfinish
    rw [bind_eq_ok_iff] at hfinish
    obtain ⟨⟨entry, rest⟩, hpop, hfinish⟩ := hfinish
    dsimp! only at hfinish
    cases entry with
    | none =>
      simp [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hfinish
    | some entry =>
      simp only [core.option.Option.ok_or, maybeArced_arced, bind_tc_ok] at hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨empty, hempty, hfinish⟩ := hfinish
      cases empty with
      | false => simp at hfinish
      | true =>
        simp only [↓reduceIte, ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
        obtain ⟨rfl, _, _⟩ := hfinish
        have hrest : rest.val = [] := by simpa [alloc.vec.Vec.is_empty] using hempty
        have hcontents := Builder.finish_tree_elements ValueInst self nextIndex htree
        rw [Builder.elements, vec_pop_some_values hpop, hrest] at hcontents
        simpa only [_root_.List.nil_append, stackElements_singleton] using hcontents

/-- **Builder finish contents.** Every successful result contains exactly the
    pending forest's sequence, including partial packed leaves and zero
    padding. No builder invariant or element law is needed for preservation
    itself; the existing invariant separately establishes density and length. -/
theorem Builder.finish_elements {T : Type} (ValueInst : Value T) (self : Builder T)
    {output : tree.Tree T} {depth : Std.Usize} {length : utils.Length}
    (hfinish : Builder.finish ValueInst self = ok (core.result.Result.Ok (output, depth, length))) :
    output.elements = self.elements := by
  unfold Builder.finish at hfinish
  rw [bind_eq_ok_iff] at hfinish
  obtain ⟨empty, hempty, hfinish⟩ := hfinish
  cases empty with
  | true =>
    simp [tree.Tree.zero, triomphe.arc.Arc.new] at hfinish
    obtain ⟨rfl, _, _⟩ := hfinish
    have hstack : self.stack.val = [] := by simpa [alloc.vec.Vec.is_empty] using hempty
    simp [Builder.elements, tree.Tree.elements, hstack]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, utils.Length.as_usize, bind_tc_ok] at hfinish
    rw [bind_eq_ok_iff] at hfinish
    obtain ⟨levelCapacity, _, hfinish⟩ := hfinish
    rw [bind_eq_ok_iff] at hfinish
    obtain ⟨nextIndex, _, hfinish⟩ := hfinish
    cases hfactor : self.packing_factor with
    | none =>
      rw [hfactor] at hfinish
      exact finishTail_elements ValueInst self nextIndex hfinish
    | some factor =>
      rw [hfactor, bind_eq_ok_iff] at hfinish
      obtain ⟨remainder, _, hfinish⟩ := hfinish
      simp only [lift, bind_tc_ok] at hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨skip, _, hfinish⟩ := hfinish
      split at hfinish
      · split at hfinish
        · rw [bind_eq_ok_iff] at hfinish
          obtain ⟨⟨status, packed⟩, hpacked, hfinish⟩ := hfinish
          dsimp! only at hfinish
          cases status with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hfinish
          | Ok success =>
            cases success
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hfinish
            rw [bind_eq_ok_iff] at hfinish
            obtain ⟨next, _, hfinish⟩ := hfinish
            exact (finishTail_elements ValueInst packed next hfinish).trans
              (Builder.finish_packed_leaf_elements ValueInst self nextIndex hpacked)
        · exact finishTail_elements ValueInst self nextIndex hfinish
      · exact finishTail_elements ValueInst self nextIndex hfinish

end milhouse.builder
