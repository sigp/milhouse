import Tree.ProgressiveList.Arbitrary.Total
import Tree.ProgressiveList.Arbitrary.Conditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The actual trait default runs the ordinary list generator and discards
only its final input state. It does not invoke Vec's take-rest override. -/
theorem ProgressiveList.arbitrary_take_rest_eq {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input : _root_.arbitrary.unstructured.Unstructured) :
    (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      (do
        let (result, _) ← ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input
        ok result) := rfl

/-- List generation has the pinned default size hint at every depth,
independently of element or update-map behavior. -/
theorem ProgressiveList.arbitrary_size_hint {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (depth : Std.Usize) :
    (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).size_hint depth =
      ok (0#usize, none) := rfl

theorem ProgressiveList.arbitrary_try_size_hint {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (depth : Std.Usize) :
    (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).try_size_hint depth =
      ok (.Ok (0#usize, none)) := rfl

/-- Owning-input generation returns precisely an ordinary generator result,
with its final input hidden. This includes every returned Rust error. -/
theorem ProgressiveList.arbitrary_take_rest_result_iff {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input : _root_.arbitrary.unstructured.Unstructured)
    (result : core.result.Result (ProgressiveList T U) arbitrary.error.Error) :
    (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok result ↔
    ∃ after, ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (result, after) := by
  rw [ProgressiveList.arbitrary_take_rest_eq, builder.bind_eq_ok_iff]
  constructor
  · rintro ⟨⟨actual, after⟩, hresult, heq⟩
    simp! only [ok.injEq] at heq
    subst actual
    exact ⟨after, hresult⟩
  · rintro ⟨after, hresult⟩
    exact ⟨(result, after), hresult, rfl⟩

/-- The actual owning trait default has the same exact installed-map
representation criterion. Its ordinary generator call and discarded final
input are recovered from successful execution, not assumed. -/
theorem ProgressiveList.arbitrary_take_rest_represents_iff {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (input : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self)) :
    self.Represents ValueInst mapInst self.tree.elements ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim self.tree.elements.length
          (fun index => max (index.val + 1) self.tree.elements.length) = self.tree.elements.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates self.tree.elements self.tree.elements := by
  obtain ⟨after, hresult⟩ :=
    (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mp hresult
  exact ProgressiveList.arbitrary_represents_iff inst ValueInst mapInst hlayout input after self hresult

/-- Owning generation succeeds exactly when some actual finite generation
trace, occupied capacity, and default-map success justify its ordinary call.
Its hidden final input is existentially recovered; no trace or successful
default construction is supplied as a premise. -/
theorem ProgressiveList.arbitrary_take_rest_success_iff_inputs {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input : _root_.arbitrary.unstructured.Unstructured)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self)) ↔
      ∃ after, ∃ values : alloc.vec.Vec T, arbitrary.Generates inst input values.val after ∧
        ProgressiveTree.LengthFits factor values.val.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates := by
  constructor
  · rintro ⟨self, hresult⟩
    obtain ⟨after, hresult⟩ :=
      (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mp hresult
    exact ⟨after, (ProgressiveList.arbitrary_success_iff_inputs inst ValueInst mapInst input after hlayout).mp
      ⟨self, hresult⟩⟩
  · rintro ⟨after, hinputs⟩
    obtain ⟨self, hresult⟩ :=
      (ProgressiveList.arbitrary_success_iff_inputs inst ValueInst mapInst input after hlayout).mpr hinputs
    exact ⟨self, (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mpr
      ⟨after, hresult⟩⟩

/-- Successful owning generation represents its actual produced sequence
exactly when its finite control/element trace, occupied capacity, and actual
default-map overlay/extent conditions hold. The discarded final input remains
bound to that same trace, and no pending-emptiness law is needed. -/
theorem ProgressiveList.arbitrary_take_rest_success_represents_iff {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input : _root_.arbitrary.unstructured.Unstructured)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self) ∧ self.Represents ValueInst mapInst self.tree.elements) ↔
      ∃ after, ∃ values : alloc.vec.Vec T, arbitrary.Generates inst input values.val after ∧
        ProgressiveTree.LengthFits factor values.val.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
          (∃ largest, mapInst.max_index updates = ok largest ∧
            largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length) ∧
          ProgressiveListIter.Overlay mapInst updates values.val values.val := by
  constructor
  · rintro ⟨self, hresult, hrep⟩
    obtain ⟨after, hresult⟩ :=
      (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mp hresult
    exact ⟨after, (ProgressiveList.arbitrary_success_represents_iff inst ValueInst mapInst input after hlayout).mp
      ⟨self, hresult, hrep⟩⟩
  · rintro ⟨after, hinputs⟩
    obtain ⟨self, hresult, hrep⟩ :=
      (ProgressiveList.arbitrary_success_represents_iff inst ValueInst mapInst input after hlayout).mpr hinputs
    exact ⟨self, (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mpr
      ⟨after, hresult⟩, hrep⟩

/-- The actual owning trait method derives its complete representation and
backing/spine contract from the traced ordinary generator and the exact map
overlay/extent laws. Pending emptiness is used only for its observer. -/
theorem ProgressiveList.arbitrary_take_rest_total_spec_of_overlay {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (htrace : arbitrary.Generates inst input values.val after)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates values.val values.val)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self) ∧ self.Represents ValueInst mapInst values.val ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hresult, hrep, hbacking, hspine, hpending⟩ := ProgressiveList.arbitrary_total_spec_of_overlay
    inst ValueInst mapInst input after values htrace hlayout hfits updates hdefault hextent hoverlay hempty
  exact ⟨self, (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mpr
    ⟨after, hresult⟩, hrep, hbacking, hspine, hpending⟩

/-- The owning trait entry point has the same total indexed representation
and valid backing as ordinary generation along the same element trace. -/
theorem ProgressiveList.arbitrary_take_rest_total_spec {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (htrace : arbitrary.Generates inst input values.val after)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self) ∧ self.Represents ValueInst mapInst values.val ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  exact ProgressiveList.arbitrary_take_rest_total_spec_of_overlay inst ValueInst mapInst input after values
    htrace hlayout hfits updates hdefault ⟨none, hmax, rfl⟩
    (fun index => ⟨none, hget index, rfl⟩) hempty

/-- Every successful owning-input generator establishes valid backing,
without any element-generation trace or default-map law. -/
theorem ProgressiveList.arbitrary_take_rest_backing_valid {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (input : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : (ProgressiveList.Insts.ArbitraryArbitrary inst ValueInst mapInst).arbitrary_take_rest input =
      ok (.Ok self)) : self.BackingValid factor := by
  obtain ⟨after, hresult⟩ :=
    (ProgressiveList.arbitrary_take_rest_result_iff inst ValueInst mapInst input (.Ok self)).mp hresult
  exact ProgressiveList.arbitrary_backing_valid inst ValueInst mapInst hlayout input after self hresult

end milhouse.progressive_list
