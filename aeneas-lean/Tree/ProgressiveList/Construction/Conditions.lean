import Tree.ProgressiveList.Construction.Trace

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Iterator construction succeeds exactly when conversion and next calls
yield a finite sequence, its occupied layers fit, and the default-map call
succeeds. No finite-input or successful-default premise is imposed on this
equivalence, and no cloning or map-content law is needed. -/
theorem ProgressiveList.try_from_iter_success_iff {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) ↔
    ∃ values, IntoIteratorYields iterInst input values ∧
      ProgressiveTree.LengthFits factor values.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates := by
  constructor
  · rintro ⟨self, hnew⟩
    obtain ⟨hyields, hlength, hdefault⟩ := ProgressiveList.try_from_iter_trace
      ValueInst mapInst iterInst input hnew
    obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid
      ValueInst mapInst iterInst input hlayout hnew
    exact ⟨self.tree.elements, hyields, by simpa only [hlength] using hdense.lengthFits hfits,
      self.updates, hdefault⟩
  · rintro ⟨values, hyields, hfits, updates, hdefault⟩
    obtain ⟨self, hnew, _⟩ := ProgressiveList.try_from_iter_total
      ValueInst mapInst iterInst input values hyields hlayout hfits updates hdefault
    exact ⟨self, hnew⟩

/-- Vector construction succeeds exactly when the occupied layers fit and
the actual default map can be constructed. The vector supplies its own finite
iterator; no iterator premise or successful-default premise remains. -/
theorem ProgressiveList.new_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self)) ↔
      ProgressiveTree.LengthFits factor values.val.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates := by
  constructor
  · rintro ⟨self, hnew⟩
    obtain ⟨_, hlength, hdefault⟩ := ProgressiveList.new_contents ValueInst mapInst values hnew
    obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid ValueInst mapInst
      (core.iter.traits.collect.IntoIteratorVec T) values hlayout hnew
    exact ⟨by simpa only [hlength] using hdense.lengthFits hfits, self.updates, hdefault⟩
  · rintro ⟨hfits, updates, hdefault⟩
    obtain ⟨self, hnew, _⟩ := ProgressiveList.try_from_iter_total ValueInst mapInst
      (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values)
      hlayout hfits updates hdefault
    exact ⟨self, hnew⟩

/-- The actual vector conversion trait has the same complete success
criterion as the inherent vector constructor. -/
theorem ProgressiveList.try_from_vec_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.CoreConvertTryFromVecError.try_from ValueInst mapInst values =
      ok (core.result.Result.Ok self)) ↔
      ProgressiveTree.LengthFits factor values.val.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates :=
  ProgressiveList.new_success_iff ValueInst mapInst values hlayout

/-- The SSZ iterator-construction trait reflects and requires the same
finite input, occupied capacity, and successful default-map construction. -/
theorem ProgressiveList.ssz_try_from_iter_success_iff {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (core.result.Result.Ok self)) ↔
      ∃ values, IntoIteratorYields iterInst input values ∧
        ProgressiveTree.LengthFits factor values.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates :=
  ProgressiveList.try_from_iter_success_iff ValueInst mapInst iterInst input hlayout

end milhouse.progressive_list
