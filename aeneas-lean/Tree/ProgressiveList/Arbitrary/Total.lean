import Tree.ProgressiveList.Arbitrary.Behavior
import Tree.ProgressiveList.Construction.Capacity

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The actual generator succeeds along a finite element trace, storing the
exact generated backing sequence and length with valid geometry. Vector
collection, construction, and all intermediate bounds are proved internally.
Only the actual default-map call is needed here, without emptiness laws. -/
theorem ProgressiveList.arbitrary_total {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (htrace : arbitrary.Generates inst input values.val after)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after) ∧ self.tree.elements = values.val ∧
      self.length.val = values.val.length ∧ self.updates = updates ∧ self.BackingValid factor := by
  obtain ⟨self, hnew, helements, hlength, hupdates, hbacking⟩ :=
    ProgressiveList.try_from_iter_total ValueInst mapInst
      (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values)
      hlayout hfits updates hdefault
  exact ⟨self, (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mpr
    ⟨values, arbitrary.vector_of_generates inst values htrace, hnew⟩,
    helements, hlength, hupdates, hbacking⟩

/-- Under the default map's empty-state laws, generated lists represent every
traced value at its index, have valid backing/spine, and have no pending updates.
No clone law, element-size hint, or assumed successful milhouse call is needed. -/
theorem ProgressiveList.arbitrary_total_spec {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (htrace : arbitrary.Generates inst input values.val after)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after) ∧ self.Represents ValueInst mapInst values.val ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hnew, hrep, hbacking, hspine, hpending⟩ := ProgressiveList.new_total_spec
    ValueInst mapInst values hlayout hfits updates hdefault hget hmax hempty
  exact ⟨self, (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mpr
    ⟨values, arbitrary.vector_of_generates inst values htrace, hnew⟩,
    hrep, hbacking, hspine, hpending⟩

/-- An error after any finite successful prefix is returned unchanged with
the exact consumed input, without any packing, builder, or default-map laws. -/
theorem ProgressiveList.arbitrary_rejects {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (error : arbitrary.error.Error) (htrace : arbitrary.Rejects inst input values.val error after) :
    ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Err error, after) :=
  ProgressiveList.arbitrary_of_vector_error inst ValueInst mapInst input after error
    (arbitrary.vector_of_rejects inst values htrace)

/-- Given a finite generated vector and a terminating default map, success
holds exactly when its occupied progressive layers have representable capacity.
The bound in the total generator theorem is therefore necessary as well. -/
theorem ProgressiveList.arbitrary_success_iff_length_fits {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (htrace : arbitrary.Generates inst input values.val after)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    (∃ self, ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) ↔ ProgressiveTree.LengthFits factor values.val.length := by
  have hvector := arbitrary.vector_of_generates inst values htrace
  rw [← ProgressiveList.new_success_iff_length_fits ValueInst mapInst values hlayout updates hdefault]
  constructor
  · rintro ⟨self, hresult⟩
    obtain ⟨actual, hactual, hnew⟩ :=
      (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
    rw [hvector] at hactual
    cases hactual
    exact ⟨self, hnew⟩
  · rintro ⟨self, hnew⟩
    exact ⟨self, (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mpr
      ⟨values, hvector, hnew⟩⟩

end milhouse.progressive_list
