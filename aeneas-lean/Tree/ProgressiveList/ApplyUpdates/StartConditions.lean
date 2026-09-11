import Tree.ProgressiveList.ApplyUpdates.EnabledConditions
import Tree.ProgressiveList.ApplyUpdates.Activation

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Exact existence criterion for valid materialization
on the nonempty branch. Start conditions, occupied capacity, positive layer
selection, skipped-value agreement, and an actual default outcome are necessary
and sufficient under the remaining input and selected external laws. No start
condition or successful update is assumed upfront. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    have henabled := ProgressiveList.apply_updates_nonempty_layer_enabled
      ValueInst mapInst self hlayout hbacking.1.shape
      (fun maximum hmax layer start binary hvisit =>
        (hrange maximum hmax layer start binary hvisit).selectsValues) hempty happly
    obtain ⟨hfits, hconditions, hdefault⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_enabled
        ValueInst mapInst self contents hlayout hclone hqueries henabled hrange hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements⟩
    exact ⟨hfits, fun maximum hmax => ⟨henabled maximum hmax, hconditions maximum hmax⟩, hdefault⟩
  · rintro ⟨hfits, hconditions, hdefault⟩
    exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_enabled
      ValueInst mapInst self contents hlayout hclone hqueries
      (fun maximum hmax => (hconditions maximum hmax).1) hrange hrep hbacking hempty).mpr
      ⟨hfits, fun maximum hmax => (hconditions maximum hmax).2, hdefault⟩

/-- Exact existence criterion for valid materialization and final representation
on the nonempty branch. Start conditions, occupied capacity, positive layer
selection, skipped-value agreement, and an actual default outcome are necessary
and sufficient under the remaining input and selected external laws. No start
condition or successful update is assumed upfront. Representation additionally
requires exact default extent and self-overlay. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents := by
  constructor
  · rintro ⟨result, happly, hafter, helements, hresult⟩
    have henabled := ProgressiveList.apply_updates_nonempty_layer_enabled
      ValueInst mapInst self hlayout hbacking.1.shape
      (fun maximum hmax layer start binary hvisit =>
        (hrange maximum hmax layer start binary hvisit).selectsValues) hempty happly
    obtain ⟨hfits, hconditions, hdefault⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_enabled
        ValueInst mapInst self contents hlayout hclone hqueries henabled hrange hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements, hresult⟩
    exact ⟨hfits, fun maximum hmax => ⟨henabled maximum hmax, hconditions maximum hmax⟩, hdefault⟩
  · rintro ⟨hfits, hconditions, hdefault⟩
    exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_enabled
      ValueInst mapInst self contents hlayout hclone hqueries
      (fun maximum hmax => (hconditions maximum hmax).1) hrange hrep hbacking hempty).mpr
      ⟨hfits, fun maximum hmax => (hconditions maximum hmax).2, hdefault⟩

/-- Exact existence criterion for valid materialization
on both branches. Start conditions, occupied capacity, positive layer
selection, skipped-value agreement, and an actual default outcome are necessary
and sufficient under the remaining input and selected external laws. No start
condition or successful update is assumed upfront. The no-op requires only valid
input backing already storing the contents. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : mapInst.is_empty self.updates = ok false → self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.BackingValid factor ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
              ValueInst mapInst self.updates maximum 0#u32 ∧
            self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
            self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults) := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, rfl⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl ⟨hempty, hafter, helements⟩
    · exact Or.inr ⟨hempty,
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff
          ValueInst mapInst self contents (hlayout hempty) (hclone hempty) (hqueries hempty)
          (hrange hempty) (hrep hempty) (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff
        ValueInst mapInst self contents (hlayout hempty) (hclone hempty) (hqueries hempty)
        (hrange hempty) (hrep hempty) (hbacking hempty) hempty).mpr hconditions

/-- Exact existence criterion for valid materialization and final representation
on both branches. Start conditions, occupied capacity, positive layer
selection, skipped-value agreement, and an actual default outcome are necessary
and sufficient under the remaining input and selected external laws. No start
condition or successful update is assumed upfront. Representation additionally
requires exact default extent and self-overlay. The no-op requires only valid
input backing already storing the contents. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.BackingValid factor ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
              ValueInst mapInst self.updates maximum 0#u32 ∧
            self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
            self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents) := by
  constructor
  · rintro ⟨result, happly, hafter, helements, hresult⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, rfl⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl ⟨hempty, hafter, helements⟩
    · exact Or.inr ⟨hempty,
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff
          ValueInst mapInst self contents (hlayout hempty) (hclone hempty) (hqueries hempty)
          (hrange hempty) hrep (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements, hresult⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements, hrep⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff
        ValueInst mapInst self contents (hlayout hempty) (hclone hempty) (hqueries hempty)
        (hrange hempty) hrep (hbacking hempty) hempty).mpr hconditions

end milhouse.progressive_list
