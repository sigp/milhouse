import Tree.ProgressiveList.ApplyUpdates.SkippedConditions
import Tree.ProgressiveList.ApplyUpdates.GuardConditions
import Tree.ProgressiveList.ApplyUpdates.StoredClones

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


/-- Exact criterion for successful valid materialization with no upfront
clone or termination law. Selected clone conditions are necessary as well as
sufficient: all copied storage terminates, while retained slots and pending
values preserve their identities. No range-value reflection is required;
positive numeric binary selection, layout, and input invariants remain upfront.
Missing-update guards and all skipped-value agreements belong to the criterion. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hbinarySelected : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
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
        self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
          ValueInst mapInst self.updates maximum 0#u32 ∧
        self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32 ∧
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly, hafter, helements⟩
    have hmaterialized := (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_clones_skipped
      ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty happly).mp
      ⟨hafter, helements⟩
    have hqueries := ProgressiveList.apply_updates_nonempty_queries_terminate
      ValueInst mapInst self hlayout hempty happly
    have hstored := ProgressiveList.apply_updates_nonempty_stored_clones_terminate
      ValueInst mapInst self hlayout hempty happly
    have hguards := ProgressiveList.apply_updates_nonempty_guards_pass
      ValueInst mapInst self hlayout hbacking.1.shape hempty happly
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    have hfits := hafter.1.lengthFits hafter.2
    rw [hlength] at hfits
    refine ⟨hfits, ?_, result.updates, installed_default ValueInst mapInst self hempty happly⟩
    intro maximum hmax
    obtain ⟨hretained, hremaining⟩ := hmaterialized maximum hmax
    exact ⟨hqueries maximum hmax,
      (ProgressiveTree.BulkCloneLaws.iff_stored_and_retained ValueInst mapInst self.updates
        factor maximum self.tree 0#u32).mpr ⟨hstored maximum hmax, hretained⟩,
      hguards maximum hmax, hremaining⟩
  · rintro ⟨hfits, hconditions, defaults, hdefault⟩
    obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success_of_guards
      ValueInst mapInst self contents hlayout
      (fun maximum hmax => (hconditions maximum hmax).2.1.terminates)
      (fun maximum hmax => (hconditions maximum hmax).1)
      (fun maximum hmax => (hconditions maximum hmax).2.2.1)
      hrep hbacking.1 hfits hempty defaults hdefault
    refine ⟨result, happly, (ProgressiveList.apply_updates_nonempty_backing_valid_contents_iff_clones_skipped
      ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty happly).mpr ?_⟩
    intro maximum hmax
    obtain ⟨_, hclones, _, hremaining⟩ := hconditions maximum hmax
    exact ⟨hclones.preserves, hremaining⟩

/-- Exact criterion for successful valid materialization and representation,
without range-value reflection or upfront clone/termination laws. Positive
numeric binary selection remains upfront. The actual default map must have
exact logical extent and overlay the final stored contents with themselves. -/
theorem ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hbinarySelected : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
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
    obtain ⟨hfits, hconditions, _⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection
        ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty).mp
        ⟨result, happly, hafter, helements⟩
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    refine ⟨hfits, hconditions, result.updates, installed_default ValueInst mapInst self hempty happly, ?_⟩
    simpa only [helements, hlength] using
      (ProgressiveList.represents_iff_overlay_of_length ValueInst mapInst hlayout result contents
        hafter.1 hafter.2 hlength).mp hresult
  · rintro ⟨hfits, hconditions, defaults, hdefault, hextent, hoverlay⟩
    obtain ⟨result, happly, hafter, helements⟩ :=
      (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection
        ValueInst mapInst self contents hlayout hbinarySelected hrep hbacking hempty).mpr
        ⟨hfits, hconditions, defaults, hdefault⟩
    have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    have hdefaults : result.updates = defaults :=
      Result.ok.inj ((installed_default ValueInst mapInst self hempty happly).symm.trans hdefault)
    refine ⟨result, happly, hafter, helements,
      (ProgressiveList.represents_iff_overlay_of_length ValueInst mapInst hlayout result contents
        hafter.1 hafter.2 hlength).mpr ?_⟩
    simpa only [hdefaults, helements, hlength] using And.intro hextent hoverlay

/-- Both branches of valid materialization, without upfront clone or
termination laws. The no-op requires valid backing already storing the contents;
all rebuilding conditions belong only to the nonempty criterion. Positive
numeric binary selection is the remaining upfront range condition. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_iff_of_binary_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : mapInst.is_empty self.updates = ok false → self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hbinarySelected : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
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
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection
          ValueInst mapInst self contents (hlayout hempty)
          (hbinarySelected hempty) (hrep hempty) (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_iff_of_binary_selection
        ValueInst mapInst self contents (hlayout hempty)
        (hbinarySelected hempty) (hrep hempty) (hbacking hempty) hempty).mpr hconditions

/-- Both branches of valid materialization and representation, without
upfront clone or termination laws. The no-op uses input representation; the
rebuilding criterion includes the actual default map's exact extent and overlay.
No range-value reflection is required; positive numeric binary selection remains
upfront only on the rebuilding branch. -/
theorem ProgressiveList.apply_updates_success_valid_materializes_represents_iff_of_binary_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hbinarySelected : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
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
        (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_selection
          ValueInst mapInst self contents (hlayout hempty)
          (hbinarySelected hempty) hrep (hbacking hempty) hempty).mp
          ⟨result, happly, hafter, helements, hresult⟩⟩
  · rintro (⟨hempty, hafter, helements⟩ | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
        hafter, helements, hrep⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_valid_materializes_represents_iff_of_binary_selection
        ValueInst mapInst self contents (hlayout hempty)
        (hbinarySelected hempty) hrep (hbacking hempty) hempty).mpr hconditions

end milhouse.progressive_list
