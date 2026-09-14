import Tree.ProgressiveList.ApplyUpdates.Contents
import Tree.ProgressiveList.Backing
import Tree.ProgressiveTree.BulkUpdate.Density
import Tree.ProgressiveTree.BulkUpdate.LayerSelection

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

/-- Successful application preserves backing validity under numeric range
conditions at all reached progressive and binary windows. No range answer
must reflect pending-value presence or absence. The represented sequence supplies the dense update domain, and the
checked length supplies the maximum extent. No clone or default-map law is needed. -/
theorem ProgressiveList.apply_updates_preserves_backing_of_all_range_extents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hlayers : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn
        (update_map.RangePreservesExtentAt mapInst self.updates self.length.val contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn
        (update_map.RangePreservesExtentAt mapInst self.updates self.length.val contents.length)
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
    exact progressive_tree.ProgressiveTree.with_updated_leaves_dense_of_all_range_extents ValueInst mapInst self.updates
      (hlayout hempty) hextent hdomain (by simpa only [hcontentsLength] using hlayers hempty)
      (by simpa only [hcontentsLength] using hrange hempty) hbacking.1 hbacking.2 hupdate

/-- Successful application preserves backing validity under numeric range
conditions at progressive layers and reflection only inside selected binary
subtrees. The represented sequence supplies the dense update domain, and the
checked length supplies the maximum extent. No clone or default-map law is needed. -/
theorem ProgressiveList.apply_updates_preserves_backing_of_range_extents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hlayers : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn
        (update_map.RangePreservesExtentAt mapInst self.updates self.length.val contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  exact ProgressiveList.apply_updates_preserves_backing_of_all_range_extents
    ValueInst mapInst self contents hlayout hlayers
    (fun hempty maximum hmax layer start binary hvisit =>
      (hrange hempty maximum hmax layer start binary hvisit).mono
        (fun _ _ h => h.preservesExtent hrep.dense_update_domain))
    hrep hbacking happly

/-- Agreement with original values in skipped progressive and binary ranges
supplies every false-answer extent law. Positive answers need only select an
occupied final window. This preserves backing validity without range-value
reflection or clone laws, including unchanged empty-map application. -/
theorem ProgressiveList.apply_updates_preserves_backing_of_skipped_ranges {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hselected : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hagreement : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hbinarySelected : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hbinaryAgreement : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  apply ProgressiveList.apply_updates_preserves_backing_of_all_range_extents
    ValueInst mapInst self contents hlayout _ _ hrep hbacking happly
  · intro hempty maximum hmax
    exact (hagreement hempty maximum hmax).preservesExtents (hlayout hempty)
      (by simpa [progressive_tree.progressiveCapacity] using hbacking.1)
      hbacking.2 hrep.dense_update_domain.length_mono hrep.extension_complete (hselected hempty maximum hmax)
  · intro hempty maximum hmax
    exact (hbinaryAgreement hempty maximum hmax).preservesExtents (hlayout hempty)
      (by simpa [progressive_tree.progressiveCapacity] using hbacking.1)
      hrep.dense_update_domain.length_mono hrep.extension_complete (hbinarySelected hempty maximum hmax)

/-- Skipped-layer agreement supplies false-answer extents from the input
representation and backing invariant. The remaining progressive range law
constrains only positive answers, on nonempty application. -/
theorem ProgressiveList.apply_updates_preserves_backing_of_layer_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hselected : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hagreement : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  apply ProgressiveList.apply_updates_preserves_backing_of_range_extents ValueInst mapInst self contents
    hlayout _ hrange hrep hbacking happly
  intro hempty maximum hmax
  exact (hagreement hempty maximum hmax).preservesExtents (hlayout hempty)
    (by simpa [progressive_tree.progressiveCapacity] using hbacking.1)
    hbacking.2 hrep.dense_update_domain.length_mono hrep.extension_complete (hselected hempty maximum hmax)

/-- A dense backing produced by actual nonempty application forces every
selected progressive layer to begin inside its new prefix. No input sequence,
input backing invariant, clone, range, or default-map law is required. -/
theorem ProgressiveList.apply_updates_nonempty_layer_selection_of_dense_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result))
    (hdense : result.tree.Dense factor 0 result.length.val) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates result.length.val)
        ValueInst mapInst self.updates maximum 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · exact progressive_tree.ProgressiveTree.with_updated_leaves_layer_selection
      ValueInst mapInst self.updates hlayout hupdate hdense

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
  exact ProgressiveList.apply_updates_preserves_backing_of_range_extents ValueInst mapInst self contents
    hlayout
    (fun hempty maximum hmax => (hrange hempty maximum hmax).layers
      (fun _ _ h => h.preservesExtent hrep.dense_update_domain))
    (fun hempty maximum hmax => (hrange hempty maximum hmax).binary_layers)
    hrep hbacking happly

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
