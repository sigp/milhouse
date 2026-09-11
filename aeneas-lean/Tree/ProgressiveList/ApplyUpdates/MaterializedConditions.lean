import Tree.ProgressiveList.ApplyUpdates.Capacity
import Tree.ProgressiveList.ApplyUpdates.Skipped

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Actual nonempty application succeeds and stores exactly the merged
sequence iff occupied capacity fits, skipped pending values agree with backing,
and default construction succeeds. None of those conditions is assumed upfront;
selected clone/range and input backing laws suffice to prove the equivalence. -/
theorem ProgressiveList.apply_updates_nonempty_success_materializes_iff {T U : Type}
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
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.tree.elements = contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly, helements⟩
    have hfits := ProgressiveList.length_fits_after_nonempty_apply_updates ValueInst mapInst self contents
      hlayout hrange hrep hbacking hempty happly
    have hskipped := (ProgressiveList.apply_updates_nonempty_backing_contents_iff_skipped
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mp helements
    have hdefault : mapInst.coredefaultDefaultInst.default = ok result.updates := by
      rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
        ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, hdefault, _, _, rfl⟩
      · rw [hempty] at htrue
        cases htrue
      · exact hdefault
    exact ⟨hfits, hskipped, result.updates, hdefault⟩
  · rintro ⟨hfits, hskipped, defaults, hdefault⟩
    obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success ValueInst mapInst
      self contents hlayout (fun maximum hmax => (hclone maximum hmax).terminates)
      hqueries hrange hrep hbacking.1 hfits hempty defaults hdefault
    have helements := (ProgressiveList.apply_updates_nonempty_backing_contents_iff_skipped
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mpr hskipped
    exact ⟨result, happly, helements⟩

/-- Successful materialization and final sequence representation jointly
require exactly occupied capacity, skipped-value agreement, and an actual
default outcome with matching overlay and extent, under the selected clone/range
and input backing laws. Pending emptiness is independent of these properties. -/
theorem ProgressiveList.apply_updates_nonempty_success_materializes_represents_iff {T U : Type}
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
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents := by
  constructor
  · rintro ⟨result, happly, helements, hresult⟩
    have hfits := ProgressiveList.length_fits_after_nonempty_apply_updates ValueInst mapInst self contents
      hlayout hrange hrep hbacking hempty happly
    have hskipped := (ProgressiveList.apply_updates_nonempty_backing_contents_iff_skipped
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mp helements
    have hdefault : mapInst.coredefaultDefaultInst.default = ok result.updates := by
      rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
        ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, hdefault, _, _, rfl⟩
      · rw [hempty] at htrue
        cases htrue
      · exact hdefault
    refine ⟨hfits, hskipped, result.updates, hdefault, ?_⟩
    simpa only [helements] using
      (ProgressiveList.apply_updates_nonempty_represents_iff ValueInst mapInst self contents
        hlayout hrange hrep hbacking hempty happly).mp hresult
  · rintro ⟨hfits, hskipped, defaults, hdefault, hextent, hoverlay⟩
    obtain ⟨result, happly, _, hdefaults⟩ := ProgressiveList.apply_updates_nonempty_success ValueInst mapInst
      self contents hlayout (fun maximum hmax => (hclone maximum hmax).terminates)
      hqueries hrange hrep hbacking.1 hfits hempty defaults hdefault
    have helements := (ProgressiveList.apply_updates_nonempty_backing_contents_iff_skipped
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
      hrange hrep hbacking hempty happly).mpr hskipped
    refine ⟨result, happly, helements,
      (ProgressiveList.apply_updates_nonempty_represents_iff ValueInst mapInst self contents
        hlayout hrange hrep hbacking hempty happly).mpr ?_⟩
    simpa only [hdefaults, helements] using And.intro hextent hoverlay

/-- Complete successful materialization also accounts for the empty-map
no-op: that branch stores the target sequence exactly when the input backing
already does. All geometry, clone, range, and backing laws are conditional on
nonempty application; branch-answer termination is not assumed. -/
theorem ProgressiveList.apply_updates_success_materializes_iff {T U : Type}
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
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.tree.elements = contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults) := by
  constructor
  · rintro ⟨result, happly, helements⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, rfl⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl ⟨hempty, helements⟩
    · exact Or.inr ⟨hempty,
        (ProgressiveList.apply_updates_nonempty_success_materializes_iff ValueInst mapInst self contents
          (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty)
          hrep (hbacking hempty) hempty).mp ⟨result, happly, helements⟩⟩
  · rintro (⟨hempty, helements⟩ | ⟨hempty, hinputs⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty, helements⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_materializes_iff ValueInst mapInst self contents
        (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty)
        hrep (hbacking hempty) hempty).mpr hinputs

/-- Complete public execution with both exact stored contents and sequence
representation. The empty-map no-op requires the backing already to contain
the merged sequence. Otherwise final capacity, skipped-value agreement, and
an actual default overlay/extent characterize success under the selected laws. -/
theorem ProgressiveList.apply_updates_success_materializes_represents_iff {T U : Type}
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
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents) := by
  constructor
  · rintro ⟨result, happly, helements, hresult⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, rfl⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl ⟨hempty, helements⟩
    · exact Or.inr ⟨hempty,
        (ProgressiveList.apply_updates_nonempty_success_materializes_represents_iff ValueInst mapInst self contents
          (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty)
          hrep (hbacking hempty) hempty).mp ⟨result, happly, helements, hresult⟩⟩
  · rintro (⟨hempty, helements⟩ | ⟨hempty, hinputs⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty, helements, hrep⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_materializes_represents_iff ValueInst mapInst self contents
        (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty)
        hrep (hbacking hempty) hempty).mpr hinputs

end milhouse.progressive_list
