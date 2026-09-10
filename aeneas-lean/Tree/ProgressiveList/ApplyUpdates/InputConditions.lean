import Tree.ProgressiveList.ApplyUpdates.SelectionConditions
import Tree.ProgressiveList.ApplyUpdates.BinarySelection

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Exact criterion for successful valid materialization with only layout
and input representation/backing validity upfront. All reached clone, query,
missing-update guard, numeric selection, skipped-value, occupied-capacity, and
default-success conditions are necessary and sufficient. No successful update
or external range/clone/termination law is assumed. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    have hbinarySelected := ProgressiveList.apply_updates_nonempty_binary_selection_of_dense_backing
      ValueInst mapInst self hlayout hempty happly hafter.1
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    rw [hlength] at hbinarySelected
    obtain ⟨hfits, hconditions, hdefault⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection
        ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements⟩
    exact ⟨hfits, fun maximum hmax => ⟨hbinarySelected maximum hmax, hconditions maximum hmax⟩, hdefault⟩
  · rintro ⟨hfits, hconditions, hdefault⟩
    exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hconditions maximum hmax).1)
      hrep hbacking hempty).mpr
      ⟨hfits, fun maximum hmax => (hconditions maximum hmax).2, hdefault⟩

/-- Exact valid-materialization and representation criterion without
upfront range, clone, or termination laws. Representation additionally requires
the actual installed default map's exact extent and self-overlay. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents := by
  constructor
  · rintro ⟨result, happly, hafter, helements, hresult⟩
    have hbinarySelected := ProgressiveList.apply_updates_nonempty_binary_selection_of_dense_backing
      ValueInst mapInst self hlayout hempty happly hafter.1
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    rw [hlength] at hbinarySelected
    obtain ⟨hfits, hconditions, hdefault⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_selection
        ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements, hresult⟩
    exact ⟨hfits, fun maximum hmax => ⟨hbinarySelected maximum hmax, hconditions maximum hmax⟩, hdefault⟩
  · rintro ⟨hfits, hconditions, hdefault⟩
    exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_selection
      ValueInst mapInst self contents hlayout (fun maximum hmax => (hconditions maximum hmax).1)
      hrep hbacking hempty).mpr
      ⟨hfits, fun maximum hmax => (hconditions maximum hmax).2, hdefault⟩

/-- Both materialization branches with all rebuilding conditions on the
necessary-and-sufficient side. The no-op requires valid backing already storing
the contents; layout and input representation/backing are needed only for
rebuilding. No upfront clone, range, or termination law is assumed. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_iff_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : mapInst.is_empty self.updates = ok false → self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.BackingValid factor ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
              ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkRangeOn
              (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
              ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
              ValueInst mapInst self.updates maximum 0#u32 ∧
            self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
            self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults) := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, rfl⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl ⟨hempty, hafter, helements⟩
    · exact Or.inr ⟨hempty,
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_inputs
          ValueInst mapInst self contents (hlayout hempty)
          (hrep hempty) (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_inputs
        ValueInst mapInst self contents (hlayout hempty)
        (hrep hempty) (hbacking hempty) hempty).mpr hconditions

/-- Both materialization/representation branches without upfront clone,
range, or termination laws. The no-op uses input representation; rebuilding
requires the actual default map's exact extent and self-overlay in the criterion. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_represents_iff_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.BackingValid factor ∧ result.tree.elements = contents ∧ result.Represents ValueInst mapInst contents) ↔
      (mapInst.is_empty self.updates = ok true ∧ self.BackingValid factor ∧ self.tree.elements = contents) ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          (∀ maximum, mapInst.max_index self.updates = ok maximum →
            self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
              ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkRangeOn
              (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
              ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32 ∧
            self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
              ValueInst mapInst self.updates maximum 0#u32 ∧
            self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
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
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_inputs
          ValueInst mapInst self contents (hlayout hempty)
          hrep (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements, hresult⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements, hrep⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_inputs
        ValueInst mapInst self contents (hlayout hempty)
        hrep (hbacking hempty) hempty).mpr hconditions

end milhouse.progressive_list
