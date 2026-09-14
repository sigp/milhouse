import Tree.ProgressiveList.Construction.Overlay
import Tree.ProgressiveList.Spine

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A dense backing tree with representable layers and an empty pending map
    implements its materialized sequence at every index, including out of bounds. -/
theorem ProgressiveList.represents_of_dense_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U)
    (hdense : self.tree.Dense factor 0 self.length.val)
    (hfits : self.tree.Fits factor 0)
    (hget : ∀ i, mapInst.get self.updates i = ok none)
    (hmax : mapInst.max_index self.updates = ok none) :
    self.Represents ValueInst mapInst self.tree.elements := by
  apply (ProgressiveList.represents_iff_overlay_of_length ValueInst mapInst hlayout
    self self.tree.elements hdense hfits hdense.elements_length.symm).mpr
  exact ⟨⟨none, hmax, hdense.elements_length.symm⟩, fun index => ⟨none, hget index, rfl⟩⟩

/-- Successful iterator construction represents exactly its input sequence,
    establishes the backing-spine invariant, and has no pending updates.
    Geometry and lookup bounds are proved from construction. The remaining
    premises specify the input iterator and the generic packing/default-map laws. -/
theorem ProgressiveList.try_from_iter_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ i, mapInst.get updates i = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) :
    self.Represents ValueInst mapInst values ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨_, _, hmap⟩ := ProgressiveList.try_from_iter_contents
    ValueInst mapInst iterInst input values hyields hnew
  obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid
    ValueInst mapInst iterInst input hlayout hnew
  obtain ⟨hget, hmax, hempty⟩ := hdefault self.updates hmap
  refine ⟨?_, ⟨hdense.shape, ?_⟩, ?_⟩
  · apply (ProgressiveList.try_from_iter_represents_iff ValueInst mapInst iterInst input values hyields hlayout hnew).mpr
    exact ⟨⟨none, hmax, rfl⟩, fun index => ⟨none, hget index, rfl⟩⟩
  · simpa using hdense.endsAfter
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty

/-- Vector construction represents the vector in order with its exact length,
    including out-of-bounds lookup behavior, and establishes a valid backing
    spine with no pending updates. No vector-iterator premise is required. -/
theorem ProgressiveList.new_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (values : alloc.vec.Vec T) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ i, mapInst.get updates i = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self)) :
    self.Represents ValueInst mapInst values.val ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.try_from_iter_spec ValueInst mapInst (core.iter.traits.collect.IntoIteratorVec T)
    values values.val (vec_into_iterator_yields values) hlayout hdefault hnew

end milhouse.progressive_list
