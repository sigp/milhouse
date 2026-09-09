import Tree.ProgressiveList.PopFront.Contents
import Tree.ProgressiveList.PopFront.BuilderLength

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful nonzero removal records exactly the retained element count.
Actual execution supplies all clone, default-construction, and builder
successes; no clone identity, default-map semantics, final-capacity bound, or
separately assumed removal bound is needed for this count. -/
theorem ProgressiveList.backing_length_after_nonzero_pop_front {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    result.length.val = (contents.drop n.val).length := by
  rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
    ⟨hzero, _⟩ | ⟨_, beforeLength, cursor, initial, built, output, length, updates,
      hlen, hindex, hiter, hnew, hextend, hfinish, _, rfl⟩
  · exact (hnonzero hzero).elim
  · obtain ⟨observed, hobserved, hcontentsLength⟩ := hrep.1
    rw [hlen] at hobserved
    cases hobserved
    have hbound : n.val ≤ contents.length := by scalar_tac
    obtain ⟨actualCursor, hactual, _, _, hyields⟩ := ProgressiveList.iter_from_spec
      ValueInst mapInst hlayout self contents n hrep hbacking.1 hbacking.2 hbound
    rw [hiter] at hactual
    cases hactual
    have hcount := ProgressiveListIter.extend_builder_length ValueInst mapInst cursor initial
      (contents.drop n.val) hyields hextend
    obtain ⟨hempty, hcounts⟩ := ProgressiveTreeBuilder.new_elements ValueInst hnew
    have hzero : initial.length.val = 0 := by
      simpa only [hempty, _root_.List.length_nil] using hcounts.2
    have hinitial := ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew
    have hbuilt := ProgressiveListIter.extend_builder_preserves_valid
      ValueInst mapInst cursor initial hinitial hextend
    have hlength := (ProgressiveTreeBuilder.finish_spec ValueInst built hbuilt hfinish).2.1
    change length.val = (contents.drop n.val).length
    rw [hlength]
    simpa only [hzero, Nat.zero_add] using hcount

end milhouse.progressive_list
