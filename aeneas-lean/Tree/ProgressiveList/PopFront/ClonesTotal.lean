import Tree.ProgressiveList.PopFront.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Nonzero in-bounds removal represents the actual ordered clones of the
retained suffix. Terminating clones may change values; empty-default-map laws
then establish every indexed read and the absence of pending updates. Traversal,
construction, retained length, and valid backing are all derived internally. -/
theorem ProgressiveList.pop_front_nonzero_clones_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) (hbound : n.val ≤ contents.length)
    (hclone : ∀ value ∈ contents.drop n.val,
      ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
    (hfits : ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ copied result,
      _root_.List.mapM ValueInst.corecloneCloneInst.clone (contents.drop n.val) = ok copied ∧
      ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst copied ∧ result.BackingValid factor ∧
      copied.length = (contents.drop n.val).length ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  obtain ⟨result, hpop, _, hvalid, hupdates⟩ := ProgressiveList.pop_front_nonzero_success
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hbound hclone hfits updates hdefault
  obtain ⟨_, hclones, _, _, _⟩ := ProgressiveList.pop_front_nonzero_clones
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
  refine ⟨result.tree.elements, result, hclones, hpop, ?_, hvalid,
    List.mapM_Result_length hclones, ?_⟩
  · exact ProgressiveList.represents_of_dense_backing ValueInst mapInst hlayout result hvalid.1 hvalid.2
      (by simpa only [hupdates] using hget) (by simpa only [hupdates] using hmax)
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst result true
      (by simpa only [hupdates] using hempty)

end milhouse.progressive_list
