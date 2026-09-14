import Tree.ProgressiveList.Arbitrary.Generated
import Tree.ProgressiveList.Construction.OverlayConditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Generation succeeds with a particular final input exactly when actual
control/element calls produce a finite vector, its occupied layers fit, and
the actual default-map call succeeds. No trace, default success, size hint,
element-consumption law, or intermediate milhouse call is assumed. -/
theorem ProgressiveList.arbitrary_success_iff_inputs {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) ↔
      ∃ values : alloc.vec.Vec T, arbitrary.Generates inst input values.val after ∧
        ProgressiveTree.LengthFits factor values.val.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates := by
  constructor
  · rintro ⟨self, hresult⟩
    obtain ⟨values, hvector, hnew⟩ :=
      (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
    exact ⟨values, (arbitrary.vector_success_iff_generates inst input after values).mp hvector,
      (ProgressiveList.new_success_iff ValueInst mapInst values hlayout).mp ⟨self, hnew⟩⟩
  · rintro ⟨values, htrace, hfits, hdefault⟩
    obtain ⟨self, hnew⟩ := (ProgressiveList.new_success_iff ValueInst mapInst values hlayout).mpr
      ⟨hfits, hdefault⟩
    exact ⟨self, (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mpr
      ⟨values, arbitrary.vector_of_generates inst values htrace, hnew⟩⟩

/-- Successful generation represents its actual generated sequence exactly
when the finite control/element trace and occupied capacity are accompanied by
an actual default map preserving those values through overlay and extent.
The trace and final input are tied to execution; pending emptiness is irrelevant
to this criterion, and no successful subcall is assumed. -/
theorem ProgressiveList.arbitrary_success_represents_iff {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after) ∧ self.Represents ValueInst mapInst self.tree.elements) ↔
      ∃ values : alloc.vec.Vec T, arbitrary.Generates inst input values.val after ∧
        ProgressiveTree.LengthFits factor values.val.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
          (∃ largest, mapInst.max_index updates = ok largest ∧
            largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length) ∧
          ProgressiveListIter.Overlay mapInst updates values.val values.val := by
  constructor
  · rintro ⟨self, hresult, hrep⟩
    obtain ⟨values, hvector, hnew⟩ :=
      (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
    have helements := (ProgressiveList.new_contents ValueInst mapInst values hnew).1
    exact ⟨values, (arbitrary.vector_success_iff_generates inst input after values).mp hvector,
      (ProgressiveList.new_success_represents_iff ValueInst mapInst values hlayout).mp
        ⟨self, hnew, by simpa only [helements] using hrep⟩⟩
  · rintro ⟨values, htrace, hfits, hdefault⟩
    obtain ⟨self, hnew, hrep⟩ := (ProgressiveList.new_success_represents_iff ValueInst mapInst values hlayout).mpr
      ⟨hfits, hdefault⟩
    have helements := (ProgressiveList.new_contents ValueInst mapInst values hnew).1
    exact ⟨self, (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mpr
      ⟨values, arbitrary.vector_of_generates inst values htrace, hnew⟩,
      by simpa only [helements] using hrep⟩

end milhouse.progressive_list
