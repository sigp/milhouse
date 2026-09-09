import Tree.ProgressiveList.ApplyUpdates.Contents
import Tree.ProgressiveList.Backing
import Tree.ProgressiveTree.BulkUpdate.Density

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Represented reads and length determine the complete dense pending-update
    domain. Every extension position has a pending value, and no pending value
    can lie outside the represented sequence. No extra map law is assumed. -/
theorem ProgressiveList.Represents.dense_update_domain {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T}
    {self : ProgressiveList T U} {contents : _root_.List T}
    (hrep : self.Represents ValueInst mapInst contents) :
    tree.DenseUpdateDomain self.length.val contents.length (update_map.HasValueAt mapInst self.updates) := by
  obtain ⟨length, hlength, hcontents⟩ := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · have := ProgressiveList.len_ge_backing ValueInst mapInst self length hlength
    omega
  · intro index hlo hhi
    have hbound : index < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    let query := Std.Usize.ofNatCore index hbound
    have hquery : query.val = index := Usize.ofNatCore_val_eq hbound
    obtain ⟨value, hget⟩ := hrep.extension_complete query (by omega) (by omega)
    exact ⟨query, value, hquery, hget⟩
  · rintro index ⟨query, value, hquery, hget⟩
    have hread := hrep.2 query
    rw [ProgressiveList.get_of_pending_update ValueInst mapInst self query value hget] at hread
    by_contra hnot
    rw [_root_.List.getElem?_eq_none (by omega)] at hread
    cases hread

/-- Applying pending updates preserves the full backing traversal invariant.
    The dense update domain comes from the old representation. Density and
    capacity bounds need neither identity cloning nor default-map laws. -/
theorem ProgressiveList.apply_updates_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrange : update_map.RangeReflectsValues mapInst self.updates)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨_, rfl⟩ | ⟨defaults, length, newTree, _, hlength, hupdate, rfl⟩
  · exact hbacking
  · have hlenBefore : ProgressiveList.len ValueInst mapInst self = ok length := by
      rw [ProgressiveList.len_eq_updated_length]
      exact hlength
    obtain ⟨observedLength, hobserved, hcontentsLength⟩ := hrep.1
    rw [hlenBefore] at hobserved
    cases hobserved
    have hdomain : tree.DenseUpdateDomain self.length.val length.val
        (update_map.HasValueAt mapInst self.updates) := by
      simpa only [hcontentsLength] using hrep.dense_update_domain
    exact progressive_tree.ProgressiveTree.with_updated_leaves_dense ValueInst mapInst self.updates
      hlayout hrange hmaximum hdomain hbacking.1 hbacking.2 hupdate

/-- Successful application preserves the complete represented sequence and
    backing validity and clears pending updates. The resulting invariants
    supply the premises of the public iterator and vector-collection proofs. -/
theorem ProgressiveList.apply_updates_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : update_map.RangeReflectsValues mapInst self.updates)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hdefault : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      (∀ query, mapInst.get defaults query = ok none) ∧
        mapInst.max_index defaults = ok none ∧ mapInst.is_empty defaults = ok true)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  have hshape := hbacking.1.shape
  have hends : self.tree.EndsAfter factor 0 self.length.val := by
    simpa [progressive_tree.progressiveCapacity] using hbacking.1.endsAfter
  have hnewRep := ProgressiveList.apply_updates_represents ValueInst mapInst self contents
    hlayout hclone hrange.excludesValues hmaximum
    (fun defaults h => (hdefault defaults h).1)
    (fun defaults h => (hdefault defaults h).2.1) hrep hshape hends happly
  exact ⟨hnewRep.1,
    ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
      hlayout hrange hmaximum hrep hbacking happly,
    ProgressiveList.no_pending_updates_after_apply_updates ValueInst mapInst self
      (fun defaults h => (hdefault defaults h).2.2) happly⟩

end milhouse.progressive_list
