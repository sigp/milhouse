import Tree.ProgressiveList.ApplyUpdates.Materialized
import Tree.ProgressiveTree.BulkUpdate.SkippedReads
import Tree.ProgressiveTree.BulkUpdate.LayerSkippedReads

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Correct backing reads force agreement in every progressive layer
skipped by an actual false range answer. This necessity direction needs no
input representation, packing, shape, clone, range, or default-map law. -/
theorem ProgressiveList.apply_updates_nonempty_layer_skipped_values_agree_of_backing_reads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result))
    (hreads : ∀ query value, query.val < result.length.val →
      mapInst.get self.updates query = ok (some value) →
      ProgressiveList.backing_get ValueInst mapInst result query = ok (some value)) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum result.length.val 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · apply progressive_tree.ProgressiveTree.with_updated_leaves_layer_skipped_values_agree
      ValueInst mapInst self.updates hupdate
    intro query value hhi hget
    have hread := hreads query value hhi hget
    have hindex : query < length := by scalar_tac
    simpa only [ProgressiveList.backing_get, ProgressiveList.backing_len, utils.Length.as_usize,
      bind_tc_ok, if_pos hindex, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using hread

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

/-- Under selected clone preservation and binary false-answer exclusion,
correct materialized reads are equivalent to pending-value agreement in both
skipped progressive layers and maximum-skipped suffixes. The necessity
direction uses neither law, and neither direction constrains the default map. -/
theorem ProgressiveList.apply_updates_nonempty_backing_reads_iff_layer_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    (∀ query, ProgressiveList.backing_get ValueInst mapInst result query = ok contents[query.val]?) ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  constructor
  · intro hreads
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    have hpendingReads : ∀ query value, query.val < result.length.val →
        mapInst.get self.updates query = ok (some value) →
        ProgressiveList.backing_get ValueInst mapInst result query = ok (some value) := by
      intro query value _ hget
      exact (hreads query).trans ((hrep.2 query).symm.trans
        (ProgressiveList.get_of_pending_update ValueInst mapInst self query value hget))
    have hlayers := ProgressiveList.apply_updates_nonempty_layer_skipped_values_agree_of_backing_reads
      ValueInst mapInst self hempty happly hpendingReads
    have hskipped := ProgressiveList.apply_updates_nonempty_skipped_values_agree_of_backing_reads
      ValueInst mapInst self hempty happly hpendingReads
    intro maximum hmax
    simpa only [hlength] using And.intro (hlayers maximum hmax) (hskipped maximum hmax)
  · intro hagreement
    exact (ProgressiveList.apply_updates_nonempty_backing_spec_of_layer_agreement ValueInst mapInst self contents
      hlayout hclone hrange (fun maximum hmax => (hagreement maximum hmax).1)
      (fun maximum hmax => (hagreement maximum hmax).2) hrep hshape hends hempty happly).2.2

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
  rw [ProgressiveList.apply_updates_nonempty_backing_reads_iff_layer_agreement ValueInst mapInst self contents
    hlayout hclone (fun maximum hmax => (hrange maximum hmax).binary_layers)
    hrep hshape hends hempty happly]
  constructor
  · exact fun hagreement maximum hmax => (hagreement maximum hmax).2
  · intro hskipped maximum hmax
    exact ⟨progressive_tree.ProgressiveTree.BulkLayerSkippedValuesAgree.of_ranges contents.length
      ((hrange maximum hmax).layers (fun _ _ h => h)), hskipped maximum hmax⟩

/-- Successful application has valid, exactly materialized backing iff
pending values agree in skipped layers and suffixes. Positive layer selection
and selected binary reflection suffice; no false-answer extent is assumed.
Backing validity is part of the conclusion, established in the sufficiency
direction rather than supplied as an external law. -/
theorem ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_layer_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hselected : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    (result.BackingValid factor ∧ result.tree.elements = contents) ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  constructor
  · rintro ⟨hafter, helements⟩
    apply (ProgressiveList.apply_updates_nonempty_backing_reads_iff_layer_agreement ValueInst mapInst self contents
      hlayout hclone
      (fun maximum hmax layer start binary hvisit => (hrange maximum hmax layer start binary hvisit).excludesValues)
      hrep hbacking.1.shape (by simpa using hbacking.1.endsAfter) hempty happly).mp
    intro query
    simpa only [helements] using
      ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout result hafter.1 hafter.2 query
  · intro hagreement
    have hlayers := fun maximum hmax => (hagreement maximum hmax).1
    have hskipped := fun maximum hmax => (hagreement maximum hmax).2
    exact ⟨ProgressiveList.apply_updates_preserves_backing_of_layer_agreement ValueInst mapInst self contents
      (fun _ => hlayout) (fun _ => hselected) (fun _ => hlayers) (fun _ => hrange) hrep hbacking happly,
      ProgressiveList.apply_updates_nonempty_backing_contents_of_layer_selection ValueInst mapInst self contents
        hlayout hclone hselected hrange hlayers hskipped hrep hbacking hempty happly⟩

/-- Under numeric progressive-layer extents and selected binary reflection,
exact stored materialization is equivalent to agreement in both kinds of
skipped region. Successful application supplies output density and length;
no default-map law is needed. -/
theorem ProgressiveList.apply_updates_nonempty_backing_contents_iff_layer_agreement {T U : Type}
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
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.elements = contents ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  have hafter := ProgressiveList.apply_updates_preserves_backing_of_range_extents ValueInst mapInst self contents
    (fun _ => hlayout) (fun _ => hextents) (fun _ => hrange) hrep hbacking happly
  have hiff := ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_layer_agreement
    ValueInst mapInst self contents hlayout hclone
    (fun maximum hmax start stop hquery => (hextents maximum hmax start stop hquery).selectsInside)
    hrange hrep hbacking hempty happly
  exact ⟨fun helements => hiff.mp ⟨hafter, helements⟩, fun hagreement => (hiff.mpr hagreement).2⟩

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
  rw [ProgressiveList.apply_updates_nonempty_backing_contents_iff_layer_agreement ValueInst mapInst self contents
    hlayout hclone
    (fun maximum hmax => (hrange maximum hmax).layers
      (fun _ _ h => h.preservesExtent hrep.dense_update_domain))
    (fun maximum hmax => (hrange maximum hmax).binary_layers) hrep hbacking hempty happly]
  constructor
  · exact fun hagreement maximum hmax => (hagreement maximum hmax).2
  · intro hskipped maximum hmax
    exact ⟨progressive_tree.ProgressiveTree.BulkLayerSkippedValuesAgree.of_ranges contents.length
      ((hrange maximum hmax).excludesValues.layers (fun _ _ h => h)), hskipped maximum hmax⟩

end milhouse.progressive_list
