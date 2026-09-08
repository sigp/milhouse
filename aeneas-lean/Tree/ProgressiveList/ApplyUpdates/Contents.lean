import Tree.ProgressiveList.ApplyUpdates
import Tree.ProgressiveTree.BulkUpdate.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A successful list lookup has already successfully queried the pending
    map, even if its result comes from the backing tree. -/
theorem ProgressiveList.pending_get_of_get_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {query : Std.Usize} {value : Option T}
    (hget : ProgressiveList.get ValueInst mapInst self query = ok value) :
    ∃ pending, mapInst.get self.updates query = ok pending := by
  unfold ProgressiveList.get at hget
  cases hmap : mapInst.get self.updates query with
  | fail e => simp [hmap] at hget
  | div => simp [hmap] at hget
  | ok pending => exact ⟨pending, rfl⟩

/-- Sequence representation itself guarantees every extension position has
    a pending value. Callers do not need a separate no-gap assumption. -/
theorem ProgressiveList.Represents.extension_complete {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T}
    {self : ProgressiveList T U} {contents : _root_.List T}
    (hrep : self.Represents ValueInst mapInst contents) :
    update_map.ExtensionComplete mapInst self.updates self.length.val contents.length := by
  intro query hlo hhi
  have hread := hrep.2 query
  obtain ⟨pending, hpending⟩ := ProgressiveList.pending_get_of_get_success ValueInst mapInst self hread
  cases pending with
  | some value => exact ⟨value, hpending⟩
  | none =>
    have hnone := ProgressiveList.get_none_of_backing_bound ValueInst mapInst self query hpending
      (by scalar_tac)
    rw [hnone, _root_.List.getElem?_eq_getElem hhi] at hread
    cases hread

/-- Successful application preserves the represented sequence at every index
    and preserves the structural spine invariants for the new backing length.
    Extension completeness follows from the old sequence representation; no
    additional density, arithmetic, or backing-readability premise is required. -/
theorem ProgressiveList.apply_updates_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst self.updates)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hdefaultGet : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      ∀ query, mapInst.get defaults query = ok none)
    (hdefaultMax : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.max_index defaults = ok none)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.tree.Shape factor 0 ∧
      result.tree.EndsAfter factor 0 result.length.val := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨_, rfl⟩ | ⟨defaults, length, newTree, hdefault, hlength, hupdate, rfl⟩
  · exact ⟨hrep, hshape, hends⟩
  · have hlenBefore : ProgressiveList.len ValueInst mapInst self = ok length := by
      rw [ProgressiveList.len_eq_updated_length]
      exact hlength
    obtain ⟨observedLength, hobserved, hcontentsLength⟩ := hrep.1
    rw [hlenBefore] at hobserved
    cases hobserved
    have hcomplete : update_map.ExtensionComplete mapInst self.updates self.length.val length.val := by
      simpa only [hcontentsLength] using hrep.extension_complete
    obtain ⟨hnewShape, hnewEnds, hnewContents⟩ :=
      progressive_tree.ProgressiveTree.with_updated_leaves_shape_contents ValueInst mapInst self.updates
        hlayout hclone hrange hmaximum hcomplete hshape hends hupdate
    refine ⟨⟨⟨length, ?_, hcontentsLength⟩, ?_⟩, hnewShape, hnewEnds⟩
    · exact ProgressiveList.len_of_no_max_index ValueInst mapInst _ (hdefaultMax defaults hdefault)
    · intro query
      by_cases hin : query.val < contents.length
      · rw [ProgressiveList.get_of_backing ValueInst mapInst _ query
          (hdefaultGet defaults hdefault query) (by scalar_tac)]
        have hread := hrep.2 query
        obtain ⟨pending, hpending⟩ := ProgressiveList.pending_get_of_get_success ValueInst mapInst self hread
        have hupdated := hnewContents query pending (by simp [progressive_tree.progressiveCapacity])
          (by omega) hpending
        cases pending with
        | some value =>
          have hpendingRead := ProgressiveList.get_of_pending_update ValueInst mapInst self query value hpending
          exact hupdated.trans (hpendingRead.symm.trans hread)
        | none =>
          by_cases hbacking : query < self.length
          · rw [ProgressiveList.get_of_backing ValueInst mapInst self query hpending hbacking] at hread
            exact hupdated.trans hread
          · obtain ⟨value, hvalue⟩ := hcomplete query (by scalar_tac) (by omega)
            rw [hpending] at hvalue
            cases hvalue
      · rw [ProgressiveList.get_none_of_backing_bound ValueInst mapInst _ query
          (hdefaultGet defaults hdefault query) (by scalar_tac),
          _root_.List.getElem?_eq_none (by omega)]

end milhouse.progressive_list
