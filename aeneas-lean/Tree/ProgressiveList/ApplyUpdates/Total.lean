import Tree.ProgressiveList.ApplyUpdates.Backing
import Tree.ProgressiveTree.BulkUpdate.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Nonempty application terminates and installs the computed backing length
and default map. Representation supplies lookup termination, a dense update
domain, and the bound on the actual maximum; no extra laws for those facts
are required. Cloning need only terminate for this execution theorem. -/
theorem ProgressiveList.apply_updates_nonempty_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ lo hi, ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
    (hrange : update_map.RangeReflectsValues mapInst self.updates)
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
  obtain ⟨tree, htree⟩ := ProgressiveTree.with_updated_leaves_success ValueInst mapInst self.updates
    hlayout
    (fun query => ProgressiveList.pending_get_of_get_success ValueInst mapInst self (hrep.2 query))
    hqueries hrange maximum hmax self.length.val contents.length hmaximum hrep.dense_update_domain
    hfits self.tree
    (hclone maximum hmax)
    hdense
  refine ⟨{ tree, length, updates := defaults }, ?_, hcontentsLength, rfl⟩
  simp! only [ProgressiveList.apply_updates, hempty, Bool.false_eq_true, ↓reduceIte,
    core.mem.take, hdefault, bind_tc_ok, hlength, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
    htree, triomphe.arc.Arc.new]

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
    (hqueries : ∀ lo hi, ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
    (hrange : update_map.RangeReflectsValues mapInst self.updates)
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
  obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success ValueInst mapInst
    self contents hlayout (fun maximum hmax => (hclone maximum hmax).terminates)
    hqueries hrange hrep hbacking.1 hfits
    hempty defaults hdefault
  refine ⟨result, happly, ProgressiveList.apply_updates_spec ValueInst mapInst self contents
    hlayout (fun maximum hmax => (hclone maximum hmax).preserves)
    hrange hmaximum ?_ hrep hbacking happly⟩
  intro actual hactual
  rw [hdefault] at hactual
  cases hactual
  exact ⟨hdefaultGet, hdefaultMax, hdefaultEmpty⟩

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
      ∀ lo hi, ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
    (hrange : mapInst.is_empty self.updates = ok false →
      update_map.RangeReflectsValues mapInst self.updates)
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
  obtain ⟨empty, hempty⟩ := hempty
  cases empty with
  | true =>
    exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty,
      hrep, hbacking, ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty⟩
  | false =>
    obtain ⟨defaults, hdefault, hdefaultGet, hdefaultMax, hdefaultEmpty⟩ := hdefault hempty
    exact ProgressiveList.apply_updates_nonempty_total_spec ValueInst mapInst self contents
      (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty) (hmaximum hempty)
      hrep hbacking (hfits hempty) hempty defaults hdefault hdefaultGet hdefaultMax hdefaultEmpty

end milhouse.progressive_list
