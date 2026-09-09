import Tree.ProgressiveList.ApplyUpdates.Materialized
import Tree.ProgressiveTree.BulkUpdate.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Actual nonempty application succeeds when selected unpacked/internal
layers contain a pending value; packed terminals need no such witness. False
progressive answers carry no correctness law. Representation supplies lookup
termination, the dense domain, and the numeric maximum bound. -/
theorem ProgressiveList.apply_updates_nonempty_success_of_enabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        ValueInst mapInst self.updates factor maximum 0#u32)
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
    (hdense : self.tree.Dense factor 0 self.length.val)
    (hfits : ProgressiveTree.LengthFits factor contents.length)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.length.val = contents.length ∧ result.updates = defaults := by
  obtain ⟨length, hlength, hcontentsLength⟩ := hrep.1
  rw [ProgressiveList.len_eq_updated_length] at hlength
  have hmaxSuccess : ∃ maximum, mapInst.max_index self.updates = ok maximum := by
    cases hmax : mapInst.max_index self.updates with
    | fail e => simp only [utils.updated_length, hmax, bind_tc_fail, reduceCtorEq] at hlength
    | div => simp only [utils.updated_length, hmax, bind_tc_div, reduceCtorEq] at hlength
    | ok maximum => exact ⟨maximum, rfl⟩
  obtain ⟨maximum, hmax⟩ := hmaxSuccess
  have hmaximum : ∀ last, maximum = some last → last.val < contents.length := by
    intro last hlast
    have hlengthVal := utils.updated_length_max_spec mapInst self.length self.updates last length
      (by simpa only [hlast] using hmax) hlength
    omega
  obtain ⟨tree, htree⟩ := ProgressiveTree.with_updated_leaves_success_of_enabled ValueInst mapInst self.updates
    hlayout
    (fun query => ProgressiveList.pending_get_of_get_success ValueInst mapInst self (hrep.2 query))
    maximum hmax self.length.val contents.length hmaximum hrep.dense_update_domain
    hfits self.tree
    (hclone maximum hmax)
    (hqueries maximum hmax)
    (henabled maximum hmax) (hrange maximum hmax)
    hdense
  refine ⟨{ tree, length, updates := defaults }, ?_, hcontentsLength, rfl⟩
  simp! only [ProgressiveList.apply_updates, hempty, Bool.false_eq_true, ↓reduceIte,
    core.mem.take, hdefault, bind_tc_ok, hlength, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
    htree, triomphe.arc.Arc.new]

/-- Nonempty application terminates and installs the computed backing length
and default map. Representation supplies lookup termination, a dense update
domain, and the bound on the actual maximum; no extra laws for those facts
are required. Clone termination and range-query termination are confined to
selected inputs and reached queries for the actual maximum. -/
theorem ProgressiveList.apply_updates_nonempty_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val)
    (hfits : ProgressiveTree.LengthFits factor contents.length)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.length.val = contents.length ∧ result.updates = defaults := by
  exact ProgressiveList.apply_updates_nonempty_success_of_enabled ValueInst mapInst self contents
    hlayout hclone hqueries
    (fun maximum hmax => ProgressiveTree.BulkLayerEnabled.of_ranges hlayout (hrange maximum hmax))
    (fun maximum hmax => (hrange maximum hmax).binary_layers)
    hrep hdense hfits hempty defaults hdefault

/-- Nonempty application derives execution, represented contents, valid
backing, and the pending observer using agreement only for skipped pending
values. Actual default-map overlay and extent preserve the rebuilt sequence;
pending emptiness supplies its separate observer result. -/
theorem ProgressiveList.apply_updates_nonempty_total_spec_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hfits : ProgressiveTree.LengthFits factor contents.length)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults)
    (hextent : ∃ largest, mapInst.max_index defaults = ok largest ∧
      largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst defaults contents contents)
    (hdefaultEmpty : mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  obtain ⟨result, happly, _, hdefaults⟩ := ProgressiveList.apply_updates_nonempty_success ValueInst mapInst
    self contents hlayout (fun maximum hmax => (hclone maximum hmax).terminates)
    hqueries hrange hrep hbacking.1 hfits hempty defaults hdefault
  have helements := ProgressiveList.apply_updates_nonempty_backing_contents_of_skipped ValueInst mapInst self contents
    hlayout (fun maximum hmax => (hclone maximum hmax).preserves) hrange hskipped hrep hbacking hempty happly
  refine ⟨result, happly, ?_, ?_, ?_⟩
  · exact (ProgressiveList.apply_updates_nonempty_represents_iff ValueInst mapInst self contents
      hlayout hrange hrep hbacking hempty happly).mpr
      (by simpa only [hdefaults, helements] using And.intro hextent hoverlay)
  · exact ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
      (fun _ => hlayout) (fun _ => hrange) hrep hbacking happly
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst result true
      (by simpa only [hdefaults] using hdefaultEmpty)

/-- Nonempty application derives execution, exact sequence representation,
valid backing, and the pending observer under the default map's precise overlay
and extent laws. Selected clone preservation establishes actual stored values;
redundant matching default entries and maxima below the new length are allowed. -/
theorem ProgressiveList.apply_updates_nonempty_total_spec_of_overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hfits : ProgressiveTree.LengthFits factor contents.length)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults)
    (hextent : ∃ largest, mapInst.max_index defaults = ok largest ∧
      largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst defaults contents contents)
    (hdefaultEmpty : mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  exact ProgressiveList.apply_updates_nonempty_total_spec_of_skipped ValueInst mapInst self contents
    hlayout hclone hqueries hrange
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum maximum hmax) self.tree 0#u32)
    hrep hbacking hfits hempty defaults hdefault hextent hoverlay hdefaultEmpty

/-- Nonempty application succeeds, preserves every merged value, establishes
the updated backing invariant, and clears pending updates. Selected stored
clones need only terminate when a pending replacement discards their result;
identity is required only for retained stored slots and pending values. -/
theorem ProgressiveList.apply_updates_nonempty_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hfits : ProgressiveTree.LengthFits factor contents.length)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults)
    (hdefaultGet : ∀ query, mapInst.get defaults query = ok none)
    (hdefaultMax : mapInst.max_index defaults = ok none)
    (hdefaultEmpty : mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  exact ProgressiveList.apply_updates_nonempty_total_spec_of_overlay ValueInst mapInst self contents
    hlayout hclone hqueries hrange hmaximum hrep hbacking hfits hempty defaults hdefault
    ⟨none, hdefaultMax, rfl⟩ (fun query => ⟨none, hdefaultGet query, rfl⟩) hdefaultEmpty

/-- Complete public application under skipped-value agreement and exact
default-map laws. All rebuilding laws apply only to the actual nonempty branch;
the empty no-op bypasses cloning, geometry, ranges, and default construction. -/
theorem ProgressiveList.apply_updates_total_spec_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : ∃ empty, mapInst.is_empty self.updates = ok empty)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hskipped : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hfits : mapInst.is_empty self.updates = ok false →
      ProgressiveTree.LengthFits factor contents.length)
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
        (∃ largest, mapInst.max_index defaults = ok largest ∧
          largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
        ProgressiveListIter.Overlay mapInst defaults contents contents ∧ mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  obtain ⟨empty, hempty⟩ := hempty
  cases empty with
  | true =>
    exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
      hrep, hbacking, ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty⟩
  | false =>
    obtain ⟨defaults, hdefault, hextent, hoverlay, hdefaultEmpty⟩ := hdefault hempty
    exact ProgressiveList.apply_updates_nonempty_total_spec_of_skipped ValueInst mapInst self contents
      (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty) (hskipped hempty)
      hrep hbacking (hfits hempty) hempty defaults hdefault hextent hoverlay hdefaultEmpty

/-- Complete public application uses exact default-map overlay and extent
laws only on its nonempty rebuilding branch. The empty-map no-op bypasses all
rebuilding, default construction, and geometry queries; its existing backing
invariant is retained. Pending emptiness supplies only the observer result. -/
theorem ProgressiveList.apply_updates_total_spec_of_overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : ∃ empty, mapInst.is_empty self.updates = ok empty)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hfits : mapInst.is_empty self.updates = ok false →
      ProgressiveTree.LengthFits factor contents.length)
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
        (∃ largest, mapInst.max_index defaults = ok largest ∧
          largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
        ProgressiveListIter.Overlay mapInst defaults contents contents ∧ mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  exact ProgressiveList.apply_updates_total_spec_of_skipped ValueInst mapInst self contents
    hrep hbacking hempty hlayout hclone hqueries hrange
    (fun hempty maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum hempty maximum hmax) self.tree 0#u32)
    hfits hdefault

/-- Complete public application, including the empty-map no-op. All work
laws and capacity bounds are conditional on the nonempty branch; an empty
map needs no default construction, cloning, packing query, or range query. -/
theorem ProgressiveList.apply_updates_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : ∃ empty, mapInst.is_empty self.updates = ok empty)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hfits : mapInst.is_empty self.updates = ok false →
      ProgressiveTree.LengthFits factor contents.length)
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
        (∀ query, mapInst.get defaults query = ok none) ∧
        mapInst.max_index defaults = ok none ∧ mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  apply ProgressiveList.apply_updates_total_spec_of_overlay ValueInst mapInst self contents
    hrep hbacking hempty hlayout hclone hqueries hrange hmaximum hfits
  intro hnonempty
  obtain ⟨defaults, hdefault, hget, hmax, hempty⟩ := hdefault hnonempty
  exact ⟨defaults, hdefault, ⟨none, hmax, rfl⟩, (fun query => ⟨none, hget query, rfl⟩), hempty⟩

end milhouse.progressive_list
