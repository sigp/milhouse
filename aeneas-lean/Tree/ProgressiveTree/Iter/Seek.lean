import Tree.ProgressiveTree.Iter.Cursor

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Seeking from an unopened dense spine succeeds and establishes a valid
    cursor for its requested suffix. Density and representable layer capacity
    derive every arithmetic bound. The index is at or after this spine suffix's
    starting offset; indices beyond the logical end yield an empty cursor. -/
theorem ProgressiveTreeIter.seek_to_subtree_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (root : ProgressiveTree T) (index : Std.Usize)
    (hnode : self.current_prog_node = some root)
    (hdense : root.Dense factor self.prog_depth.val
      (self.length.val - progressiveCapacity factor self.prog_depth.val))
    (hfits : root.Fits factor self.prog_depth.val)
    (hstart : progressiveCapacity factor self.prog_depth.val ≤ index.val)
    (hyielded : self.yielded = index) :
    ∃ next, ProgressiveTreeIter.seek_to_subtree ValueInst self index = ok next ∧
      ProgressiveTreeIter.Valid ValueInst factor next
        (root.elements.drop (index.val - progressiveCapacity factor self.prog_depth.val)) ∧
      next.length = self.length ∧ next.yielded = self.yielded := by
  induction root generalizing self with
  | ProgressiveZero =>
    refine ⟨{ self with current_prog_node := none, current_iter := none }, ?_, ?_, rfl, rfl⟩
    · rw [ProgressiveTreeIter.seek_to_subtree, ProgressiveTreeIter.seek_to_subtree_loop, loop]
      simp! only [ProgressiveTreeIter.seek_to_subtree_loop.body, ProgressiveTreeIter.seek_step,
        hnode, bind_tc_ok, Bool.false_eq_true, if_false]
    · refine ⟨[], [], rfl, rfl, ?_, ?_⟩
      · simp [ProgressiveTree.elements]
      · simp [ProgressiveTree.elements]
  | ProgressiveNode hash left right ih =>
    obtain ⟨depth, binary, hdepth, hbinary, hbinaryVal, _⟩ :=
      next_layer_bounds ValueInst hlayout self.prog_depth hfits.1
    have hdepthVal : depth.val = self.prog_depth.val + 1 := by
      have hadd := UScalar.add_equiv self.prog_depth 1#u32
      rw [hdepth] at hadd
      simp at hadd
      omega
    obtain ⟨start, stop, hstartCall, hstop, hstartVal, hstopVal, _⟩ :=
      ProgressiveTree.layer_window ValueInst hlayout hdepth hbinary (by simpa [hbinaryVal] using hfits.1)
    rw [hbinaryVal] at hstopVal
    have hstopCapacity : stop.val = progressiveCapacity factor (self.prog_depth.val + 1) := by
      rw [progressiveCapacity_succ, hstopVal, hstartVal]
    by_cases hroute : index < stop
    · have hlocalBound : index.val - progressiveCapacity factor self.prog_depth.val ≤
          subtreeCapacity factor (2 * self.prog_depth.val) := by
        have hrouteVal := (UScalar.lt_equiv _ _).mp hroute
        omega
      obtain ⟨localIndex, hlocal, hlocalVal, _⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := index) (y := start) (by scalar_tac))
      have hlocalNat : localIndex.val = index.val - progressiveCapacity factor self.prog_depth.val := by
        simpa [hstartVal] using hlocalVal
      obtain ⟨nextDepth, current, henter, hnextDepth, hdrains⟩ :=
        ProgressiveTreeIter.enter_subtree_drains ValueInst hlayout self left right hash hdense hfits.1 localIndex
      refine ⟨{ self with current_prog_node := some right, current_iter := some current, prog_depth := nextDepth },
        ?_, ?_, rfl, rfl⟩
      · rw [ProgressiveTreeIter.seek_to_subtree, ProgressiveTreeIter.seek_to_subtree_loop, loop]
        simp! only [ProgressiveTreeIter.seek_to_subtree_loop.body, ProgressiveTreeIter.seek_step,
          hnode, hstartCall, hdepth, hstop, bind_tc_ok, if_pos hroute,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hlocal, henter,
          Bool.false_eq_true, if_false]
      · refine ⟨left.elements.drop localIndex.val, right.elements, hdrains, ?_, ?_, ?_⟩
        · simp only [ProgressiveTreeIter.Pending, hnextDepth]
          exact ⟨hdense.right_remainder, hfits.2, trivial⟩
        · rw [hlocalNat]
          exact hdense.drop_within_layer hlocalBound
        · have hlength := hdense.elements_length
          simp only [_root_.List.length_drop]
          simp only [hyielded]
          omega
    · have hrouteVal : stop.val ≤ index.val := by
        simpa only [UScalar.le_equiv] using le_of_not_gt hroute
      have hlocalBound : subtreeCapacity factor (2 * self.prog_depth.val) ≤
          index.val - progressiveCapacity factor self.prog_depth.val := by omega
      obtain ⟨next, hseek, hvalid, hlength, hyield⟩ := ih
        { self with current_prog_node := some right, prog_depth := depth } rfl
        (by simpa [hdepthVal] using hdense.right_remainder)
        (by simpa [hdepthVal] using hfits.2)
        (by simpa [hdepthVal, ← hstopCapacity] using hrouteVal)
        hyielded
      refine ⟨next, ?_, ?_, hlength, hyield⟩
      · rw [ProgressiveTreeIter.seek_to_subtree, ProgressiveTreeIter.seek_to_subtree_loop, loop]
        simp! only [ProgressiveTreeIter.seek_to_subtree_loop.body, ProgressiveTreeIter.seek_step,
          hnode, hstartCall, hdepth, hstop, bind_tc_ok, if_neg hroute,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_true]
        exact hseek
      · rw [hdense.drop_past_layer hlocalBound]
        simpa only [hdepthVal, progressiveCapacity_succ, Nat.sub_sub] using hvalid

end milhouse.progressive_tree
