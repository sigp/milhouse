import Tree.ProgressiveList.ApplyUpdates.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Exact stored materialization under numeric progressive-layer extents,
reflection only in selected binary subtrees, and pending-value agreement in
skipped layers and suffixes. Density identifies the stored sequence from the
derived backing reads; the installed default map is unconstrained. -/
theorem ProgressiveList.apply_updates_nonempty_backing_contents_of_layer_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hextents : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn
        (update_map.RangePreservesExtentAt mapInst self.updates self.length.val contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hlayers : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.elements = contents := by
  obtain ⟨_, _, hreads⟩ := ProgressiveList.apply_updates_nonempty_backing_spec_of_layer_agreement
    ValueInst mapInst self contents hlayout hclone
    (fun maximum hmax layer start binary hvisit => (hrange maximum hmax layer start binary hvisit).excludesValues)
    hlayers hskipped hrep hbacking.1.shape (by simpa using hbacking.1.endsAfter) hempty happly
  have hafter := ProgressiveList.apply_updates_preserves_backing_of_range_extents ValueInst mapInst self contents
    (fun _ => hlayout) (fun _ => hextents) (fun _ => hrange) hrep hbacking happly
  have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
    ValueInst mapInst self contents hrep hempty happly
  have helementsLength : result.tree.elements.length = contents.length :=
    hafter.1.elements_length.trans hlength
  apply _root_.List.ext_getElem?
  intro index
  by_cases hinside : index < contents.length
  · have hbound : index < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    let query := Std.Usize.ofNatCore index hbound
    have hquery : query.val = index := Usize.ofNatCore_val_eq hbound
    have hget := ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout result hafter.1 hafter.2 query
    simpa only [hquery] using Result.ok.inj (hget.symm.trans (hreads query))
  · rw [_root_.List.getElem?_eq_none (by omega), _root_.List.getElem?_eq_none (by omega)]

/-- The complete stored sequence equals the original merged contents under
selected clone preservation and agreement of skipped pending values. Density
identifies the sequence from the actual backing reads and checked length;
no semantic maximum bound or installed-default law is required. -/
theorem ProgressiveList.apply_updates_nonempty_backing_contents_of_skipped {T U : Type}
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
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.elements = contents := by
  exact ProgressiveList.apply_updates_nonempty_backing_contents_of_layer_agreement
    ValueInst mapInst self contents hlayout hclone
    (fun maximum hmax => (hrange maximum hmax).layers
      (fun _ _ h => h.preservesExtent hrep.dense_update_domain))
    (fun maximum hmax => (hrange maximum hmax).binary_layers)
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkLayerSkippedValuesAgree.of_ranges
      contents.length ((hrange maximum hmax).excludesValues.layers (fun _ _ h => h)))
    hskipped hrep hbacking hempty happly

/-- Selected clone preservation makes the materialized backing exactly the
original merged sequence, independently of the installed default map. Every
backing read is derived from the actual rebuilding call; density then identifies
the complete stored sequence, including its length. -/
theorem ProgressiveList.apply_updates_nonempty_backing_contents {T U : Type}
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
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.elements = contents := by
  exact ProgressiveList.apply_updates_nonempty_backing_contents_of_skipped ValueInst mapInst self contents
    hlayout hclone hrange
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum maximum hmax) self.tree 0#u32)
    hrep hbacking hempty happly

end milhouse.progressive_list
