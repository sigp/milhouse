import Tree.ProgressiveTree.Iter.Cursor

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Advancing opens exactly the next binary layer, or clears the terminal
    spine. It preserves all pending values and counters and strictly reduces
    the unopened-spine measure whenever a node was present. -/
theorem ProgressiveTreeIter.advance_to_next_subtree_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (values : _root_.List T)
    (hpending : ProgressiveTreeIter.Pending factor self.length self.prog_depth
      self.current_prog_node values)
    (hbound : values.length ≤ self.length.val - self.yielded.val) :
    ∃ next, ProgressiveTreeIter.advance_to_next_subtree ValueInst self = ok next ∧
      ProgressiveTreeIter.Valid ValueInst factor next values ∧
      next.length = self.length ∧ next.yielded = self.yielded ∧
      (self.current_prog_node ≠ none →
        ProgressiveTreeIter.pendingSteps next.current_prog_node <
          ProgressiveTreeIter.pendingSteps self.current_prog_node) := by
  cases hnode : self.current_prog_node with
  | none =>
    have hvalues : values = [] := by simpa [ProgressiveTreeIter.Pending, hnode] using hpending
    subst values
    refine ⟨{ self with current_iter := none }, ?_, ?_, rfl, rfl, ?_⟩
    · simp [ProgressiveTreeIter.advance_to_next_subtree, hnode]
    · exact ⟨[], [], rfl, hpending, rfl, hbound⟩
    · simp [hnode]
  | some root =>
    obtain ⟨hdense, hfit, rfl⟩ := (show root.Dense factor self.prog_depth.val
        (self.length.val - progressiveCapacity factor self.prog_depth.val) ∧
        root.Fits factor self.prog_depth.val ∧ values = root.elements by
      simpa [ProgressiveTreeIter.Pending, hnode] using hpending)
    cases root with
    | ProgressiveZero =>
      refine ⟨{ self with current_iter := none, current_prog_node := none }, ?_, ?_, rfl, rfl, ?_⟩
      · simp [ProgressiveTreeIter.advance_to_next_subtree, hnode]
      · exact ⟨[], [], rfl, rfl, rfl, hbound⟩
      · simp [ProgressiveTreeIter.pendingSteps, ProgressiveTree.layerCount]
    | ProgressiveNode hash left right =>
      obtain ⟨depth, current, henter, hdepth, hyields⟩ :=
        ProgressiveTreeIter.enter_subtree_drains ValueInst hlayout self left right hash hdense hfit.1 0#usize
      refine ⟨{ self with current_prog_node := some right, current_iter := some current, prog_depth := depth },
        ?_, ?_, rfl, rfl, ?_⟩
      · simp! only [ProgressiveTreeIter.advance_to_next_subtree, hnode,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok, henter]
      · refine ⟨left.elements, right.elements, ?_, ?_, rfl, hbound⟩
        · simpa [ProgressiveTreeIter.Current] using hyields
        · simp only [ProgressiveTreeIter.Pending, hdepth]
          exact ⟨hdense.right_remainder, hfit.2, trivial⟩
      · simp [ProgressiveTreeIter.pendingSteps, ProgressiveTree.layerCount]

end milhouse.progressive_tree
