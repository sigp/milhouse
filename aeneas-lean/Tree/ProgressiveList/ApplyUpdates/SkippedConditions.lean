import Tree.ProgressiveList.ApplyUpdates.Skipped
import Tree.ProgressiveList.ApplyUpdates.RetainedClones
import Tree.ProgressiveList.ApplyUpdates.BinarySkipped
import Tree.ProgressiveList.ApplyUpdates.BinarySelection

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- After actual nonempty success, valid materialization is equivalent to
retained/pending clone identity, positive progressive selection, and agreement
in all skipped binary/progressive ranges and maximum-skipped suffixes. No
range-value or clone law is assumed upfront. Positive binary selection remains
an explicit numeric premise; neither direction constrains the default map. -/
theorem ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_clones_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hbinarySelected : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    (result.BackingValid factor ∧ result.tree.elements = contents) ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  constructor
  · rintro ⟨hafter, helements⟩
    have hclone := ProgressiveList.apply_updates_nonempty_retained_clone_identity
      ValueInst mapInst self contents hlayout hrep hbacking hempty happly hafter.1 helements
    have hbinaryAgreement := ProgressiveList.apply_updates_nonempty_binary_skipped_values_agree
      ValueInst mapInst self contents hlayout hrep hbacking hempty happly hafter.1 helements
    have hselected := ProgressiveList.apply_updates_nonempty_layer_selection_of_dense_backing
      ValueInst mapInst self hlayout hempty happly hafter.1
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    have hpendingReads : ∀ query value, query.val < result.length.val →
        mapInst.get self.updates query = ok (some value) →
        ProgressiveList.backing_get ValueInst mapInst result query = ok (some value) := by
      intro query value _ hget
      have hread := ProgressiveList.backing_get_eq_elements
        ValueInst mapInst hlayout result hafter.1 hafter.2 query
      rw [helements] at hread
      exact hread.trans ((hrep.2 query).symm.trans
        (ProgressiveList.get_of_pending_update ValueInst mapInst self query value hget))
    have hlayers := ProgressiveList.apply_updates_nonempty_layer_skipped_values_agree_of_backing_reads
      ValueInst mapInst self hempty happly hpendingReads
    have hskipped := ProgressiveList.apply_updates_nonempty_skipped_values_agree_of_backing_reads
      ValueInst mapInst self hempty happly hpendingReads
    rw [hlength] at hselected hlayers hskipped
    intro maximum hmax
    exact And.intro (hclone maximum hmax)
      ⟨hselected maximum hmax, hbinaryAgreement maximum hmax, hlayers maximum hmax, hskipped maximum hmax⟩
  · intro hconditions
    have hclone := fun maximum hmax => (hconditions maximum hmax).1
    have hselected := fun maximum hmax => (hconditions maximum hmax).2.1
    have hbinaryAgreement := fun maximum hmax => (hconditions maximum hmax).2.2.1
    have hlayers := fun maximum hmax => (hconditions maximum hmax).2.2.2.1
    have hskipped := fun maximum hmax => (hconditions maximum hmax).2.2.2.2
    exact ⟨ProgressiveList.apply_updates_preserves_backing_of_skipped_ranges
      ValueInst mapInst self contents (fun _ => hlayout) (fun _ => hselected)
      (fun _ => hlayers) (fun _ => hbinarySelected) (fun _ => hbinaryAgreement) hrep hbacking happly,
      ProgressiveList.apply_updates_nonempty_backing_contents_of_skipped_ranges
        ValueInst mapInst self contents hlayout hclone hselected hbinarySelected hbinaryAgreement
        hlayers hskipped hrep hbacking hempty happly⟩

/-- Actual successful application materializes valid backing exactly when
all selected clones, numeric selections, and skipped-value agreements hold.
Only layout and input representation/backing validity remain upfront; successful
dense output itself supplies positive binary selection. -/
theorem ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_selected_clones_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    (result.BackingValid factor ∧ result.tree.elements = contents) ↔
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 := by
  constructor
  · rintro ⟨hafter, helements⟩
    have hbinarySelected := ProgressiveList.apply_updates_nonempty_binary_selection_of_dense_backing
      ValueInst mapInst self hlayout hempty happly hafter.1
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    rw [hlength] at hbinarySelected
    have hconditions := (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_clones_skipped
      ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty happly).mp
      ⟨hafter, helements⟩
    exact fun maximum hmax => ⟨hbinarySelected maximum hmax, hconditions maximum hmax⟩
  · intro hconditions
    exact (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_clones_skipped
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hconditions maximum hmax).1)
      hrep hbacking hempty happly).mpr (fun maximum hmax => (hconditions maximum hmax).2)

end milhouse.progressive_list
