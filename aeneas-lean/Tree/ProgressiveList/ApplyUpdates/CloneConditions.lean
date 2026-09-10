import Tree.ProgressiveList.ApplyUpdates.QueryConditions
import Tree.ProgressiveList.ApplyUpdates.RetainedClones

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Exact criterion for successful valid materialization with no upfront
clone or termination law. Selected clone conditions are necessary as well as
sufficient: all copied storage terminates, while retained slots and pending
values preserve their identities. Selected binary reflection, layout, and input
invariants remain explicit. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_ranges {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
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
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerEnabled ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    have hclone := ProgressiveList.apply_updates_nonempty_retained_clone_identity
      ValueInst mapInst self contents hlayout hrep hbacking hempty happly hafter.1 helements
    obtain ⟨hfits, hconditions, hdefault⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_ranges
        ValueInst mapInst self contents hlayout hclone hrange hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements⟩
    refine ⟨hfits, ?_, hdefault⟩
    intro maximum hmax
    obtain ⟨hqueries, hstored, hremaining⟩ := hconditions maximum hmax
    exact ⟨hqueries,
      (ProgressiveTree.BulkCloneLaws.iff_stored_and_retained ValueInst mapInst self.updates
        factor maximum self.tree 0#u32).mpr ⟨hstored, hclone maximum hmax⟩, hremaining⟩
  · rintro ⟨hfits, hconditions, hdefault⟩
    apply (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_ranges
      ValueInst mapInst self contents hlayout
      (fun maximum hmax => ((hconditions maximum hmax).2.1).preserves)
      hrange hrep hbacking hempty).mpr
    refine ⟨hfits, ?_, hdefault⟩
    intro maximum hmax
    obtain ⟨hqueries, hclones, hremaining⟩ := hconditions maximum hmax
    exact ⟨hqueries,
      ((ProgressiveTree.BulkCloneLaws.iff_stored_and_retained ValueInst mapInst self.updates
        factor maximum self.tree 0#u32).mp hclones).1, hremaining⟩

/-- Exact criterion for successful valid materialization and representation,
without upfront clone or termination laws. The actual default map must have
exact logical extent and overlay the final stored contents with themselves. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_ranges {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
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
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
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
    have hclone := ProgressiveList.apply_updates_nonempty_retained_clone_identity
      ValueInst mapInst self contents hlayout hrep hbacking hempty happly hafter.1 helements
    obtain ⟨hfits, hconditions, hdefault⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_ranges
        ValueInst mapInst self contents hlayout hclone hrange hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements, hresult⟩
    refine ⟨hfits, ?_, hdefault⟩
    intro maximum hmax
    obtain ⟨hqueries, hstored, hremaining⟩ := hconditions maximum hmax
    exact ⟨hqueries,
      (ProgressiveTree.BulkCloneLaws.iff_stored_and_retained ValueInst mapInst self.updates
        factor maximum self.tree 0#u32).mpr ⟨hstored, hclone maximum hmax⟩, hremaining⟩
  · rintro ⟨hfits, hconditions, hdefault⟩
    apply (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_ranges
      ValueInst mapInst self contents hlayout
      (fun maximum hmax => ((hconditions maximum hmax).2.1).preserves)
      hrange hrep hbacking hempty).mpr
    refine ⟨hfits, ?_, hdefault⟩
    intro maximum hmax
    obtain ⟨hqueries, hclones, hremaining⟩ := hconditions maximum hmax
    exact ⟨hqueries,
      ((ProgressiveTree.BulkCloneLaws.iff_stored_and_retained ValueInst mapInst self.updates
        factor maximum self.tree 0#u32).mp hclones).1, hremaining⟩

/-- Both branches of valid materialization, without upfront clone or
termination laws. The no-op requires valid backing already storing the contents;
all rebuilding clone conditions belong only to the nonempty criterion. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_iff_of_ranges {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : mapInst.is_empty self.updates = ok false → self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.BackingValid factor ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkRangeOn
              (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
              ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
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
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_ranges
          ValueInst mapInst self contents (hlayout hempty)
          (hrange hempty) (hrep hempty) (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_ranges
        ValueInst mapInst self contents (hlayout hempty)
        (hrange hempty) (hrep hempty) (hbacking hempty) hempty).mpr hconditions

/-- Both branches of valid materialization and representation, without
upfront clone or termination laws. The no-op uses input representation; the
rebuilding criterion includes the actual default map's exact extent and overlay. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_represents_iff_of_ranges {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.BackingValid factor ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkRangeOn
              (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
              ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
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
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_ranges
          ValueInst mapInst self contents (hlayout hempty)
          (hrange hempty) hrep (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements, hresult⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements, hrep⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_ranges
        ValueInst mapInst self contents (hlayout hempty)
        (hrange hempty) hrep (hbacking hempty) hempty).mpr hconditions

end milhouse.progressive_list
