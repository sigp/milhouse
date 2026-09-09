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
  obtain ⟨self, hnew, _, _, _, hbacking⟩ := ProgressiveList.try_from_iter_total ValueInst mapInst
    iterInst input values hyields hlayout hfits updates hdefault
  obtain ⟨hrep, hspine, hpending⟩ := ProgressiveList.try_from_iter_spec ValueInst mapInst
    iterInst input values hyields hlayout (fun actual hactual => by
      rw [hdefault] at hactual
      cases Result.ok.inj hactual
      exact ⟨hget, hmax, hempty⟩) hnew
  exact ⟨self, hnew, hrep, hbacking, hspine, hpending⟩

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
