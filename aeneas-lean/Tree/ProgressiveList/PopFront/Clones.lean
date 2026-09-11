import Tree.ProgressiveList.PopFront.State
import Tree.ProgressiveList.Backing

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful nonzero removal rebuilds the exact ordered clones of the
retained suffix and installs the actual default map. Success supplies the
removal bound, every clone, and every builder/default call; clone identity,
default-map semantics, and a final-capacity premise are unnecessary. -/
theorem ProgressiveList.pop_front_nonzero_clones {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    n.val ≤ contents.length ∧
      _root_.List.mapM ValueInst.corecloneCloneInst.clone (contents.drop n.val) = ok result.tree.elements ∧
      result.length.val = (contents.drop n.val).length ∧
      mapInst.coredefaultDefaultInst.default = ok result.updates ∧ result.BackingValid factor := by
  rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
    ⟨hzero, _⟩ | ⟨_, beforeLength, cursor, initial, built, output, length, updates,
      hlen, hindex, hiter, hnew, hextend, hfinish, hmap, rfl⟩
  · exact (hnonzero hzero).elim
  · obtain ⟨observed, hobserved, hcontentsLength⟩ := hrep.1
    rw [hlen] at hobserved
    cases hobserved
    have hbound : n.val ≤ contents.length := by scalar_tac
    obtain ⟨actualCursor, hactual, _, _, hyields⟩ := ProgressiveList.iter_from_spec
      ValueInst mapInst hlayout self contents n hrep hbacking.1 hbacking.2 hbound
    rw [hiter] at hactual
    cases hactual
    obtain ⟨copied, hcopied, helements, hcount⟩ := ProgressiveListIter.extend_builder_clones
      ValueInst mapInst cursor initial (contents.drop n.val) hyields hextend
    obtain ⟨hempty, hcounts⟩ := ProgressiveTreeBuilder.new_elements ValueInst hnew
    have hzero : initial.length.val = 0 := by
      simpa only [hempty, _root_.List.length_nil] using hcounts.2
    have hinitial := ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew
    have hbuilt := ProgressiveListIter.extend_builder_preserves_valid
      ValueInst mapInst cursor initial hinitial hextend
    obtain ⟨houtput, hlength, hdense, hfits⟩ := ProgressiveTreeBuilder.finish_spec ValueInst built hbuilt hfinish
    have hvalues : output.elements = copied := by
      rw [houtput, helements, hempty, _root_.List.nil_append]
    refine ⟨hbound, ?_, ?_, hmap, hdense, hfits⟩
    · simpa only [hvalues] using hcopied
    · change length.val = (contents.drop n.val).length
      rw [hlength]
      simpa only [hzero, Nat.zero_add] using hcount

end milhouse.progressive_list
