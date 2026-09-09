import Tree.ProgressiveList.PopFront.Contents
import Tree.ProgressiveList.PopFront.BuilderTotal
import Tree.ProgressiveTree.Builder.New
import Tree.ProgressiveTree.Builder.FinishSuccess

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Nonzero front removal succeeds and returns exactly the retained suffix,
with valid rebuilt backing and no pending updates. Clone laws concern only
retained values, and capacity is needed only for that rebuilt suffix. Actual
iteration and every builder success are established internally. -/
theorem ProgressiveList.pop_front_nonzero_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) (hbound : n.val ≤ contents.length)
    (hclone : ∀ value ∈ contents.drop n.val, ValueInst.corecloneCloneInst.clone value = ok value)
    (hfits : ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  have hindex : ¬ n > length := by change ¬ length.val < n.val; omega
  obtain ⟨cursor, hiter, _, _, hyields⟩ := ProgressiveList.iter_from_spec ValueInst mapInst hlayout
    self contents n hrep hbacking.1 hbacking.2 hbound
  obtain ⟨initial, hnew, hvalid, hemptyTree, hzero⟩ := ProgressiveTreeBuilder.new_spec ValueInst hlayout
  obtain ⟨built, hextend, hvalidBuilt, hbuilt, _⟩ := ProgressiveListIter.extend_builder_total_spec
    ValueInst mapInst cursor initial (contents.drop n.val) hyields hclone hvalid
    (by simpa only [hzero, Nat.zero_add] using hfits)
  obtain ⟨output, hfinish, helements, hdense, hcapacity⟩ :=
    ProgressiveTreeBuilder.finish_total_spec ValueInst built hvalidBuilt
  have houtput : output.elements = contents.drop n.val := by
    simpa only [hbuilt, hemptyTree, _root_.List.nil_append] using helements
  let result : ProgressiveList T U := { tree := output, length := built.length, updates }
  refine ⟨result, ?_, ?_, ⟨hdense, hcapacity⟩, ?_⟩
  · simp! only [ProgressiveList.pop_front, hnonzero, ↓reduceIte, hlen, hindex, hiter, hnew,
      hextend, hfinish, core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new,
      hdefault, bind_tc_ok]
    rfl
  · rw [← houtput]
    exact ProgressiveList.represents_of_dense_backing ValueInst mapInst hlayout result hdense
      hcapacity hget hmax
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst result true hempty

/-- Front removal within the logical length terminates and preserves exactly
the retained suffix. A zero removal is the original list and requires no packing,
clone, capacity, or default-map law. Nonzero removal rebuilds and clears pending
updates using only the retained values' laws and capacities. -/
theorem ProgressiveList.pop_front_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hlayout : n ≠ 0#usize → tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbound : n.val ≤ contents.length)
    (hclone : n ≠ 0#usize → ∀ value ∈ contents.drop n.val,
      ValueInst.corecloneCloneInst.clone value = ok value)
    (hfits : n ≠ 0#usize → ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (hdefault : n ≠ 0#usize → ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
      (∀ index, mapInst.get updates index = ok none) ∧
      mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true) :
    ∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      (n ≠ 0#usize → ProgressiveList.has_pending_updates ValueInst mapInst result = ok false) := by
  by_cases hzero : n = 0#usize
  · subst n
    refine ⟨self, ?_, ?_, hbacking, by simp⟩
    · simp only [ProgressiveList.pop_front, ↓reduceIte]
    · simpa only [show (0#usize).val = 0 from rfl, _root_.List.drop_zero] using hrep
  · obtain ⟨updates, hmap, hget, hmax, hempty⟩ := hdefault hzero
    obtain ⟨result, hpop, hcontents, hvalid, hpending⟩ :=
      ProgressiveList.pop_front_nonzero_total_spec ValueInst mapInst (hlayout hzero) self contents n hrep hbacking
        hzero hbound (hclone hzero) (hfits hzero) updates hmap hget hmax hempty
    exact ⟨result, hpop, hcontents, hvalid, fun _ => hpending⟩

end milhouse.progressive_list
