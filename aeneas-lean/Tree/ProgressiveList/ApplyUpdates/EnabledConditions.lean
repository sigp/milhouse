import Tree.ProgressiveList.ApplyUpdates.MaterializedConditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

private theorem installed_default {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hempty : mapInst.is_empty self.updates = ok false)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    mapInst.coredefaultDefaultInst.default = ok result.updates := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, hdefault, _, _, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · exact hdefault

/-- Nonempty application can produce valid, exactly materialized backing
iff occupied capacity fits, positive selection and skipped-value agreement
hold, and default construction succeeds. Start conditions and binary reflection
supply execution; no success, capacity, materialization, or default outcome is
assumed upfront. Packed terminals may start without pending entries. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_enabled {T U : Type}
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
    (henabled : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32)
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
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    have hfits := hafter.1.lengthFits hafter.2
    rw [hlength] at hfits
    have hconditions := (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mp ⟨hafter, helements⟩
    exact ⟨hfits, hconditions, result.updates, installed_default ValueInst mapInst self hempty happly⟩
  · rintro ⟨hfits, hconditions, defaults, hdefault⟩
    obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success_of_enabled
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).terminates)
      hqueries henabled hrange hrep hbacking.1 hfits hempty defaults hdefault
    have hmaterialized := (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mpr hconditions
    exact ⟨result, happly, hmaterialized⟩

/-- Valid materialization and final representation can both be achieved
exactly when capacity and layer conditions hold and the actual default outcome
preserves extent and overlays the contents to themselves. Pending emptiness is
independent, and no successful execution or default outcome is assumed. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_enabled {T U : Type}
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
    (henabled : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32)
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
    obtain ⟨hfits, hconditions, _⟩ := (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_enabled
      ValueInst mapInst self contents hlayout hclone hqueries henabled hrange hrep hbacking hempty).mp
      ⟨result, happly, hafter, helements⟩
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    refine ⟨hfits, hconditions, result.updates, installed_default ValueInst mapInst self hempty happly, ?_⟩
    simpa only [helements, hlength] using
      (ProgressiveList.represents_iff_overlay_of_length ValueInst mapInst hlayout result contents
        hafter.1 hafter.2 hlength).mp hresult
  · rintro ⟨hfits, hconditions, defaults, hdefault, hextent, hoverlay⟩
    obtain ⟨result, happly, hlength, hdefaults⟩ := ProgressiveList.apply_updates_nonempty_success_of_enabled
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).terminates)
      hqueries henabled hrange hrep hbacking.1 hfits hempty defaults hdefault
    obtain ⟨hafter, helements⟩ := (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mpr hconditions
    refine ⟨result, happly, hafter, helements,
      (ProgressiveList.represents_iff_overlay_of_length ValueInst mapInst hlayout result contents
        hafter.1 hafter.2 hlength).mpr ?_⟩
    simpa only [hdefaults, helements, hlength] using And.intro hextent hoverlay

end milhouse.progressive_list
