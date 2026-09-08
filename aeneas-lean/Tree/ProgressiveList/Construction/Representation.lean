import Tree.ProgressiveList.Construction
import Tree.ProgressiveList.Spine
import Tree.ProgressiveTree.Lookup

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
  have hlength := hdense.elements_length
  refine ⟨⟨self.length, ProgressiveList.len_of_no_max_index ValueInst mapInst self hmax,
    hlength.symm⟩, ?_⟩
  intro index
  by_cases hinside : index < self.length
  · rw [ProgressiveList.get_of_backing ValueInst mapInst self index (hget index) hinside]
    simpa using ProgressiveTree.Dense.get_recursive_eq_elements ValueInst hlayout
      (depth := 0#u32) hdense hfits index
  · rw [ProgressiveList.get_none_of_backing_bound ValueInst mapInst self index (hget index) hinside]
    have hbound : self.tree.elements.length ≤ index.val := by
      have : ¬ index.val < self.length.val := by simpa only [UScalar.lt_equiv] using hinside
      omega
    rw [_root_.List.getElem?_eq_none_iff.mpr hbound]

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
  obtain ⟨helements, _, hmap⟩ := ProgressiveList.try_from_iter_contents
    ValueInst mapInst iterInst input values hyields hnew
  obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid
    ValueInst mapInst iterInst input hlayout hnew
  obtain ⟨hget, hmax, hempty⟩ := hdefault self.updates hmap
  refine ⟨?_, ⟨hdense.shape, ?_⟩, ?_⟩
  · rw [← helements]
    exact ProgressiveList.represents_of_dense_backing ValueInst mapInst hlayout self hdense hfits hget hmax
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
