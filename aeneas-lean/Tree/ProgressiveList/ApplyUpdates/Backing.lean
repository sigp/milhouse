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
    capacity bounds need neither identity cloning nor default-map laws.
    The actual checked length calculation supplies the maximum's numeric
    extension bound; no law bounding pending values by that maximum remains.
    Packing and reached range laws apply only to the nonempty branch. -/
theorem ProgressiveList.apply_updates_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨_, rfl⟩ | ⟨defaults, length, newTree, hempty, _, hlength, hupdate, rfl⟩
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
    have hextent : ∀ maximum, mapInst.max_index self.updates = ok maximum →
        length.val ≤ maximum.elim self.length.val (fun last => max (last.val + 1) self.length.val) := by
      intro maximum hmax
      obtain ⟨actual, hactual, hvalue⟩ :=
        (utils.updated_length_eq_ok_iff mapInst self.length self.updates length).mp hlength
      have heq : actual = maximum := Result.ok.inj (hactual.symm.trans hmax)
      simpa only [heq] using Nat.le_of_eq hvalue.symm
    exact progressive_tree.ProgressiveTree.with_updated_leaves_dense_of_extent ValueInst mapInst self.updates
      (hlayout hempty) hextent hdomain (hrange hempty) hbacking.1 hbacking.2 hupdate

/-- Successful application preserves the complete represented sequence and
    backing validity and clears pending updates. The resulting invariants
    supply the premises of the public iterator and vector-collection proofs.
    All work laws are conditional on the nonempty branch. -/
theorem ProgressiveList.apply_updates_spec {T U : Type}
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
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
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
    hlayout hclone (fun hempty maximum hmax => (hrange hempty maximum hmax).excludesValues) hmaximum
    (fun hempty defaults h => (hdefault hempty defaults h).1)
    (fun hempty defaults h => (hdefault hempty defaults h).2.1) hrep hshape hends happly
  exact ⟨hnewRep.1,
    ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
      hlayout hrange hrep hbacking happly,
    ProgressiveList.no_pending_updates_after_apply_updates ValueInst mapInst self
      (fun hempty defaults h => (hdefault hempty defaults h).2.2) happly⟩

end milhouse.progressive_list
