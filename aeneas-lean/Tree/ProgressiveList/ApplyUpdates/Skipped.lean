import Tree.ProgressiveList.ApplyUpdates.Materialized
import Tree.ProgressiveTree.BulkUpdate.SkippedReads
import Tree.ProgressiveTree.BulkUpdate.LayerSkippedReads

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Correct backing reads for present pending values force agreement in the
suffixes skipped by actual nonempty application. This necessity direction
needs no input representation, packing, shape, clone, range, or default-map law. -/
theorem ProgressiveList.apply_updates_nonempty_skipped_values_agree_of_backing_reads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result))
    (hreads : ∀ query value, query.val < result.length.val →
      mapInst.get self.updates query = ok (some value) →
      ProgressiveList.backing_get ValueInst mapInst result query = ok (some value)) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum result.length.val 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · apply progressive_tree.ProgressiveTree.with_updated_leaves_skipped_values_agree
      ValueInst mapInst self.updates hupdate
    intro query value hhi hget
    have hread := hreads query value hhi hget
    have hindex : query < length := by scalar_tac
    simpa only [ProgressiveList.backing_get, ProgressiveList.backing_len, utils.Length.as_usize,
      bind_tc_ok, if_pos hindex, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using hread

/-- Under the selected clone and reached range laws, correct materialized
backing reads are equivalent to skipped-value agreement. Only the sufficiency
direction uses those laws; no default-map behavior is constrained. -/
theorem ProgressiveList.apply_updates_nonempty_backing_reads_iff_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    (∀ query, ProgressiveList.backing_get ValueInst mapInst result query = ok contents[query.val]?) ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  constructor
  · intro hreads
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    have hskipped := ProgressiveList.apply_updates_nonempty_skipped_values_agree_of_backing_reads
      ValueInst mapInst self hempty happly (by
        intro query value _ hget
        exact (hreads query).trans ((hrep.2 query).symm.trans
          (ProgressiveList.get_of_pending_update ValueInst mapInst self query value hget)))
    simpa only [hlength] using hskipped
  · intro hskipped
    exact (ProgressiveList.apply_updates_nonempty_backing_spec_of_skipped ValueInst mapInst self contents
      hlayout hclone hrange hskipped hrep hshape hends hempty happly).2.2

/-- Exact stored materialization is equivalent to skipped-value agreement
under the selected clone/range and input backing laws. The actual successful
update supplies output density and length; no default-map law is needed. -/
theorem ProgressiveList.apply_updates_nonempty_backing_contents_iff_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.elements = contents ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  constructor
  · intro helements
    have hafter := ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
      (fun _ => hlayout) (fun _ => hrange) hrep hbacking happly
    apply (ProgressiveList.apply_updates_nonempty_backing_reads_iff_skipped ValueInst mapInst self contents
      hlayout hclone (fun maximum hmax => (hrange maximum hmax).excludesValues)
      hrep hbacking.1.shape (by simpa using hbacking.1.endsAfter) hempty happly).mp
    intro query
    simpa only [helements] using
      ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout result hafter.1 hafter.2 query
  · intro hskipped
    exact ProgressiveList.apply_updates_nonempty_backing_contents_of_skipped ValueInst mapInst self contents
      hlayout hclone hrange hskipped hrep hbacking hempty happly

end milhouse.progressive_list
