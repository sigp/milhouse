import Tree.ProgressiveList.PopFront.State
import Tree.ProgressiveList.Backing

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful front removal preserves backing density and representable
    capacities, without assumptions about iterator contents, map laws, or clone
    identity. Rebuilding establishes these properties from a fresh builder. -/
theorem ProgressiveList.pop_front_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (n : Std.Usize) (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
    ⟨_, rfl⟩ | ⟨_, beforeLength, cursor, initial, built, output, length, updates,
      _, _, _, hnew, hextend, hfinish, _, rfl⟩
  · exact hbacking
  · have hinitial := ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew
    have hbuilt := ProgressiveListIter.extend_builder_preserves_valid ValueInst mapInst cursor initial hinitial hextend
    exact (ProgressiveTreeBuilder.finish_spec ValueInst built hbuilt hfinish).2.2

/-- Successful `pop_front n` represents exactly the old sequence with its first
    `n` values removed, with a valid backing tree. A nonzero removal clears
    pending updates. Clone identity is needed only for the retained suffix;
    iterator completeness and every indexed-read bound are derived internally. -/
theorem ProgressiveList.pop_front_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hclone : ∀ value ∈ contents.drop n.val, ValueInst.corecloneCloneInst.clone value = ok value)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ i, mapInst.get updates i = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      (n ≠ 0#usize → ProgressiveList.has_pending_updates ValueInst mapInst result = ok false) := by
  rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
    ⟨rfl, rfl⟩ | ⟨hnonzero, beforeLength, cursor, initial, built, output, length, updates,
      hlen, hindex, hiter, hnew, hextend, hfinish, hmap, rfl⟩
  · exact ⟨by simpa using hrep, hbacking, by simp⟩
  · obtain ⟨observedLength, hobserved, hcontentsLength⟩ := hrep.1
    rw [hlen] at hobserved
    cases hobserved
    have hbound : n.val ≤ contents.length := by scalar_tac
    obtain ⟨actualCursor, hactual, _, _, hyields⟩ :=
      ProgressiveList.iter_from_spec ValueInst mapInst hlayout self contents n hrep hbacking.1 hbacking.2 hbound
    rw [hiter] at hactual
    cases hactual
    have hinitial := ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew
    have hbuilt := ProgressiveListIter.extend_builder_preserves_valid ValueInst mapInst cursor initial hinitial hextend
    obtain ⟨helements, _⟩ := ProgressiveListIter.extend_builder_contents ValueInst mapInst cursor initial
      (contents.drop n.val) hyields hclone hextend
    have hempty := (ProgressiveTreeBuilder.new_elements ValueInst hnew).1
    obtain ⟨houtput, _, hdense, hfits⟩ := ProgressiveTreeBuilder.finish_spec ValueInst built hbuilt hfinish
    have hcontents : output.elements = contents.drop n.val := by
      rw [houtput, helements, hempty, _root_.List.nil_append]
    obtain ⟨hget, hmax, hemptyMap⟩ := hdefault updates hmap
    refine ⟨?_, ⟨hdense, hfits⟩, ?_⟩
    · rw [← hcontents]
      exact ProgressiveList.represents_of_dense_backing ValueInst mapInst hlayout _ hdense hfits hget hmax
    · intro _
      exact ProgressiveList.has_pending_updates_spec ValueInst mapInst _ true hemptyMap

end milhouse.progressive_list
