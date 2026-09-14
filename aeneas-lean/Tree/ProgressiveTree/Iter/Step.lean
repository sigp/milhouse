import Tree.ProgressiveTree.Iter.Advance

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

private theorem next_step_empty_eq {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeIter T)
    (hcurrent : ProgressiveTreeIter.Current ValueInst self.current_iter []) :
    ProgressiveTreeIter.next_step ValueInst self =
      if self.current_prog_node.isSome then do
        let next ← ProgressiveTreeIter.advance_to_next_subtree ValueInst self
        ok (core.ops.control_flow.ControlFlow.Continue (), next)
      else ok (core.ops.control_flow.ControlFlow.Break none, self) := by
  cases hc : self.current_iter with
  | none =>
    simp! [ProgressiveTreeIter.next_step, hc, core.option.Option.is_some]
  | some current =>
    have hdrains : IteratorDrains
        (iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst) current [] := by
      simpa [ProgressiveTreeIter.Current, hc] using hcurrent
    cases hdrains with
    | nil hnext =>
      have hrestore : { self with current_iter := some current } = self := by
        cases self
        simp_all
      simp! [ProgressiveTreeIter.next_step, hc, hnext, hrestore, core.option.Option.is_some]

/-- Each progressive step either opens a smaller pending spine without losing
    values, or returns the next value and preserves the cursor for its tail.
    All binary calls and yielded-counter arithmetic succeed by the invariant. -/
theorem ProgressiveTreeIter.next_step_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (values : _root_.List T)
    (hvalid : ProgressiveTreeIter.Valid ValueInst factor self values) :
    ∃ flow next, ProgressiveTreeIter.next_step ValueInst self = ok (flow, next) ∧
      next.length = self.length ∧
      match flow with
      | .Continue _ =>
        ProgressiveTreeIter.Valid ValueInst factor next values ∧
          next.yielded = self.yielded ∧
          ProgressiveTreeIter.pendingSteps next.current_prog_node <
            ProgressiveTreeIter.pendingSteps self.current_prog_node
      | .Break value =>
        value = values.head? ∧ ProgressiveTreeIter.Valid ValueInst factor next values.tail ∧
          next.yielded.val = self.yielded.val + min 1 values.length := by
  obtain ⟨currentValues, pendingValues, hcurrent, hpending, rfl, hbound⟩ := hvalid
  cases currentValues with
  | nil =>
    simp only [_root_.List.nil_append] at hbound ⊢
    have hstep := next_step_empty_eq ValueInst self hcurrent
    cases hn : self.current_prog_node with
    | none =>
      have hvalues : pendingValues = [] := by
        simpa [ProgressiveTreeIter.Pending, hn] using hpending
      subst pendingValues
      refine ⟨.Break none, self, ?_, rfl, rfl, ?_, by simp⟩
      · simpa [hn] using hstep
      · exact ⟨[], [], hcurrent, hpending, rfl, hbound⟩
    | some root =>
      obtain ⟨next, hadvance, hnext, hlength, hyielded, hdecrease⟩ :=
        ProgressiveTreeIter.advance_to_next_subtree_spec ValueInst hlayout self pendingValues hpending hbound
      refine ⟨.Continue (), next, ?_, hlength, hnext, hyielded, ?_⟩
      · simpa [hn, hadvance] using hstep
      · simpa [hn] using hdecrease (by simp [hn])
  | cons value currentValues =>
    cases hc : self.current_iter with
    | none => simp [ProgressiveTreeIter.Current, hc] at hcurrent
    | some current =>
      have hdrains : IteratorDrains
          (iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
          current (value :: currentValues) := by
        simpa [ProgressiveTreeIter.Current, hc] using hcurrent
      cases hdrains with
      | @cons _ rest _ _ hnext htail =>
        obtain ⟨yielded, hyielded, hyieldedVal⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := self.yielded) (y := 1#usize) (by
            simp only [_root_.List.length_append, _root_.List.length_cons] at hbound
            scalar_tac))
        refine ⟨.Break (some value), { self with current_iter := some rest, yielded },
          ?_, rfl, rfl, ?_, ?_⟩
        · simp! only [ProgressiveTreeIter.next_step, hc, hnext, bind_tc_ok, hyielded]
        · refine ⟨currentValues, pendingValues, htail, hpending, rfl, ?_⟩
          simp only [_root_.List.cons_append, _root_.List.length_cons,
            _root_.List.tail_cons] at hbound ⊢
          have hyieldedNat : yielded.val = self.yielded.val + 1 := by simpa using hyieldedVal
          omega
        · simpa using hyieldedVal

end milhouse.progressive_tree
