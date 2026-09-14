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

/-- Successful nonempty application materializes merged reads when pending
values already agree with unchanged backing in skipped progressive layers
and suffixes, including skipped ranges inside selected binary subtrees.
No range-value exclusion or reflection law is required.
The checked length supplies the numeric bound, and input representation
supplies extension completeness. No default-map or density law is needed. -/
theorem ProgressiveList.apply_updates_nonempty_backing_spec_of_skipped_ranges {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hbinaryAgreement : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32)
    (hlayers : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.Shape factor 0 ∧ result.tree.EndsAfter factor 0 result.length.val ∧
      ∀ query, ProgressiveList.backing_get ValueInst mapInst result query = ok contents[query.val]? := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, hlength, hupdate, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · obtain ⟨observed, hobserved, hcontentsLength⟩ := hrep.1
    rw [ProgressiveList.len_eq_updated_length, hlength] at hobserved
    cases hobserved
    have hcomplete : update_map.ExtensionComplete mapInst self.updates self.length.val length.val := by
      simpa only [hcontentsLength] using hrep.extension_complete
    have hextent : ∀ maximum, mapInst.max_index self.updates = ok maximum →
        length.val ≤ maximum.elim self.length.val (fun last => max (last.val + 1) self.length.val) := by
      intro maximum hmax
      obtain ⟨actual, hactual, hvalue⟩ :=
        (utils.updated_length_eq_ok_iff mapInst self.length self.updates length).mp hlength
      have heq : actual = maximum := Result.ok.inj (hactual.symm.trans hmax)
      simpa only [heq] using Nat.le_of_eq hvalue.symm
    obtain ⟨hnewShape, hnewEnds, hnewContents⟩ :=
      progressive_tree.ProgressiveTree.with_updated_leaves_shape_contents_of_skipped_ranges ValueInst mapInst self.updates
        hlayout hclone hbinaryAgreement hextent (by simpa only [hcontentsLength] using hlayers)
        (by simpa only [hcontentsLength] using hskipped)
        hcomplete hshape hends hupdate
    refine ⟨hnewShape, hnewEnds, ?_⟩
    intro query
    by_cases hin : query.val < contents.length
    · have hindex : query < length := by scalar_tac
      simp only [ProgressiveList.backing_get, ProgressiveList.backing_len, utils.Length.as_usize,
        bind_tc_ok, if_pos hindex, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
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
    · have hindex : ¬ query < length := by scalar_tac
      have hnone : contents[query.val]? = none := _root_.List.getElem?_eq_none (by omega)
      simp only [ProgressiveList.backing_get, ProgressiveList.backing_len, utils.Length.as_usize,
        bind_tc_ok, if_neg hindex, hnone]

/-- Successful nonempty application materializes merged reads when pending
values already agree with unchanged backing in skipped progressive layers
and suffixes. False-answer exclusion remains only on selected binary queries.
The checked length supplies the numeric bound, and input representation
supplies extension completeness. No default-map or density law is needed. -/
theorem ProgressiveList.apply_updates_nonempty_backing_spec_of_layer_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hlayers : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.Shape factor 0 ∧ result.tree.EndsAfter factor 0 result.length.val ∧
      ∀ query, ProgressiveList.backing_get ValueInst mapInst result query = ok contents[query.val]? := by
  exact ProgressiveList.apply_updates_nonempty_backing_spec_of_skipped_ranges
    ValueInst mapInst self contents hlayout hclone
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkBinarySkippedValuesAgree.of_ranges (hrange maximum hmax))
    hlayers hskipped hrep hshape hends hempty happly

/-- Actual nonempty application materializes every merged read when pending
values agree with backing only in the suffixes skipped by the maximum guard.
The checked length supplies the numeric extension bound. No default-map law
is required, and clone identity concerns only retained slots and selected values. -/
theorem ProgressiveList.apply_updates_nonempty_backing_spec_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.Shape factor 0 ∧ result.tree.EndsAfter factor 0 result.length.val ∧
      ∀ query, ProgressiveList.backing_get ValueInst mapInst result query = ok contents[query.val]? := by
  exact ProgressiveList.apply_updates_nonempty_backing_spec_of_layer_agreement ValueInst mapInst self contents
    hlayout hclone (fun maximum hmax => (hrange maximum hmax).binary_layers)
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkLayerSkippedValuesAgree.of_ranges
      contents.length ((hrange maximum hmax).layers (fun _ _ h => h)))
    hskipped hrep hshape hends hempty happly

/-- The nonempty branch materializes every merged read in the new backing
and establishes its spine shape. This concerns backing reads before the new
default map is consulted, so no default-map law is required. Clone identity
is scoped only to the retained stored slots and selected pending values. -/
theorem ProgressiveList.apply_updates_nonempty_backing_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.Shape factor 0 ∧ result.tree.EndsAfter factor 0 result.length.val ∧
      ∀ query, ProgressiveList.backing_get ValueInst mapInst result query = ok contents[query.val]? := by
  exact ProgressiveList.apply_updates_nonempty_backing_spec_of_skipped ValueInst mapInst self contents
    hlayout hclone hrange
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum maximum hmax) self.tree 0#u32)
    hrep hshape hends hempty happly

/-- Successful application preserves representation and spine under
agreement in skipped progressive layers and suffixes, with empty-default
lookup and maximum laws. Rebuilding laws apply only on the nonempty branch. -/
theorem ProgressiveList.apply_updates_represents_of_layer_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hlayers : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hskipped : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hdefaultGet : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      ∀ query, mapInst.get defaults query = ok none)
    (hdefaultMax : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.max_index defaults = ok none)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.tree.Shape factor 0 ∧
      result.tree.EndsAfter factor 0 result.length.val := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨_, rfl⟩ | ⟨defaults, length, newTree, hempty, hdefault, hlength, hupdate, rfl⟩
  · exact ⟨hrep, hshape, hends⟩
  · obtain ⟨hnewShape, hnewEnds, hreads⟩ := ProgressiveList.apply_updates_nonempty_backing_spec_of_layer_agreement
      ValueInst mapInst self contents (hlayout hempty) (hclone hempty) (hrange hempty)
      (hlayers hempty) (hskipped hempty) hrep hshape hends hempty happly
    have hcontentsLength := ProgressiveList.backing_length_after_nonempty_apply_updates
      ValueInst mapInst self contents hrep hempty happly
    refine ⟨⟨⟨length, ProgressiveList.len_of_no_max_index ValueInst mapInst _
      (hdefaultMax hempty defaults hdefault), hcontentsLength⟩, ?_⟩, hnewShape, hnewEnds⟩
    intro query
    simp only [ProgressiveList.get, hdefaultGet hempty defaults hdefault query, bind_tc_ok]
    exact hreads query

/-- Successful application preserves the sequence and spine under agreement
of pending values in skipped suffixes. All work laws apply only on nonempty
application; the empty branch preserves the original representation directly. -/
theorem ProgressiveList.apply_updates_represents_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hskipped : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hdefaultGet : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      ∀ query, mapInst.get defaults query = ok none)
    (hdefaultMax : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.max_index defaults = ok none)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.tree.Shape factor 0 ∧
      result.tree.EndsAfter factor 0 result.length.val := by
  exact ProgressiveList.apply_updates_represents_of_layer_agreement ValueInst mapInst self contents
    hlayout hclone (fun hempty maximum hmax => (hrange hempty maximum hmax).binary_layers)
    (fun hempty maximum hmax => progressive_tree.ProgressiveTree.BulkLayerSkippedValuesAgree.of_ranges
      contents.length ((hrange hempty maximum hmax).layers (fun _ _ h => h)))
    hskipped hdefaultGet hdefaultMax hrep hshape hends happly

/-- Successful application preserves the represented sequence at every index
    and preserves the structural spine invariants for the new backing length.
    Extension completeness follows from the old sequence representation; no
    additional density, arithmetic, or backing-readability premise is required.
    Packing, clone, range, maximum, and default-map laws are needed only on
    the nonempty branch that rebuilds the backing. -/
theorem ProgressiveList.apply_updates_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeExcludesValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hdefaultGet : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      ∀ query, mapInst.get defaults query = ok none)
    (hdefaultMax : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.max_index defaults = ok none)
    (hrep : self.Represents ValueInst mapInst contents)
    (hshape : self.tree.Shape factor 0) (hends : self.tree.EndsAfter factor 0 self.length.val)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.tree.Shape factor 0 ∧
      result.tree.EndsAfter factor 0 result.length.val := by
  exact ProgressiveList.apply_updates_represents_of_skipped ValueInst mapInst self contents
    hlayout hclone hrange
    (fun hempty maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum hempty maximum hmax) self.tree 0#u32)
    hdefaultGet hdefaultMax hrep hshape hends happly

end milhouse.progressive_list
