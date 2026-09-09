import Tree.ProgressiveList.Backing
import Tree.ProgressiveTree.ConstructionTotal

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Iterator construction succeeds, stores exactly the yielded sequence and
length, initializes the actual default map, and establishes valid backing.
There is no assumed successful constructor or builder call. -/
theorem ProgressiveList.try_from_iter_total {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self) ∧ self.tree.elements = values ∧
      self.length.val = values.length ∧ self.updates = updates ∧ self.BackingValid factor := by
  obtain ⟨output, length, hbuild, helements, hlength, hdense, hfits⟩ :=
    ProgressiveTree.build_from_iter_with_len_total_spec ValueInst iterInst input values hyields
      hlayout hfits
  refine ⟨{ tree := output, length, updates }, ?_, helements, hlength, rfl, hdense, hfits⟩
  simp! only [ProgressiveList.try_from_iter, hbuild, core.result.Result.Insts.CoreOpsTry.branch,
    triomphe.arc.Arc.new, hdefault, bind_tc_ok]

/-- Total iterator construction needs only a default map whose overlay and
logical extent preserve the input values. Empty-map reads and an absent
maximum are unnecessary. Pending emptiness is a separate observer law;
all construction calls and traversal invariants are derived internally. -/
theorem ProgressiveList.try_from_iter_total_spec_of_overlay {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates values values)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input = ok (.Ok self) ∧
      self.Represents ValueInst mapInst values ∧ self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hnew, _, _, hupdates, hbacking⟩ := ProgressiveList.try_from_iter_total
    ValueInst mapInst iterInst input values hyields hlayout hfits updates hdefault
  refine ⟨self, hnew, ?_, hbacking, ⟨hbacking.1.shape, ?_⟩, ?_⟩
  · apply (ProgressiveList.try_from_iter_represents_iff ValueInst mapInst iterInst input values hyields hlayout hnew).mpr
    simpa only [hupdates] using And.intro hextent hoverlay
  · simpa using hbacking.1.endsAfter
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst self true (by simpa only [hupdates] using hempty)

/-- Vector construction derives its iterator behavior and uses the exact
input-preserving overlay/extent laws for the actual default map. -/
theorem ProgressiveList.new_total_spec_of_overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates values.val values.val)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.new ValueInst mapInst values = ok (.Ok self) ∧
      self.Represents ValueInst mapInst values.val ∧ self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.try_from_iter_total_spec_of_overlay ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values)
    hlayout hfits updates hdefault hextent hoverlay hempty

/-- The actual vector-conversion trait inherits the complete overlay-based
constructor contract. It requires no assumed iterator or constructor result. -/
theorem ProgressiveList.try_from_vec_total_spec_of_overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates values.val values.val)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.CoreConvertTryFromVecError.try_from ValueInst mapInst values = ok (.Ok self) ∧
      self.Represents ValueInst mapInst values.val ∧ self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.new_total_spec_of_overlay ValueInst mapInst values hlayout hfits updates hdefault hextent hoverlay hempty

/-- The SSZ iterator-construction trait uses the same exact default-map laws
while deriving its actual backing construction and every indexed read. -/
theorem ProgressiveList.ssz_try_from_iter_total_spec_of_overlay {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates values values)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (.Ok self) ∧
      self.Represents ValueInst mapInst values ∧ self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.try_from_iter_total_spec_of_overlay ValueInst mapInst iterInst input values hyields
    hlayout hfits updates hdefault hextent hoverlay hempty

/-- Total iterator construction represents the exact input sequence at every
index, including out of bounds, with valid backing/spine and no pending updates.
Only the input iterator, packing layout, occupied capacities, and default-map
laws remain; all intermediate success and arithmetic are proved internally. -/
theorem ProgressiveList.try_from_iter_total_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  exact ProgressiveList.try_from_iter_total_spec_of_overlay ValueInst mapInst iterInst input values hyields
    hlayout hfits updates hdefault ⟨none, hmax, rfl⟩ (fun index => ⟨none, hget index, rfl⟩) hempty

/-- Vector construction succeeds and preserves every input value in order,
with valid backing and no pending updates. Its iterator behavior is derived
from the concrete vector model, so no iterator premise is exposed. -/
theorem ProgressiveList.new_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self) ∧
      self.Represents ValueInst mapInst values.val ∧ self.BackingValid factor ∧
      self.SpineValid factor ∧ ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.try_from_iter_total_spec ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values)
    hlayout hfits updates hdefault hget hmax hempty

/-- The actual `TryFrom<Vec<T>>` trait implementation has the same total
sequence, backing, and pending-state specification as the public constructor. -/
theorem ProgressiveList.try_from_vec_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.CoreConvertTryFromVecError.try_from ValueInst mapInst values =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values.val ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.new_total_spec ValueInst mapInst values hlayout hfits updates hdefault hget hmax hempty

/-- The SSZ iterator-construction trait succeeds with the exact input
sequence and valid backing. This is the actual trait body, with all builder
initialization, insertion, and finalization obligations discharged underneath. -/
theorem ProgressiveList.ssz_try_from_iter_total_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (core.result.Result.Ok self) ∧
      self.Represents ValueInst mapInst values ∧ self.BackingValid factor ∧
      self.SpineValid factor ∧ ProgressiveList.has_pending_updates ValueInst mapInst self = ok false :=
  ProgressiveList.try_from_iter_total_spec ValueInst mapInst iterInst input values hyields hlayout hfits
    updates hdefault hget hmax hempty

end milhouse.progressive_list
