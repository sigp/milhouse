import Tree.ProgressiveList.Backing
import Tree.Arbitrary.Generation

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The extracted generator preserves the external vector's input state,
propagates its errors, and maps only constructor errors to IncorrectFormat. -/
theorem ProgressiveList.arbitrary_eq {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input : _root_.arbitrary.unstructured.Unstructured) :
    ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input = (do
      let (generated, after) ← arbitrary.vector inst input
      match generated with
      | .Err error => ok (.Err error, after)
      | .Ok values =>
        let built ← ProgressiveList.new ValueInst mapInst values
        match built with
        | .Ok self => ok (.Ok self, after)
        | .Err _ => ok (.Err arbitrary.error.Error.IncorrectFormat, after)) := by
  unfold ProgressiveList.Insts.ArbitraryArbitrary.arbitrary
    alloc.vec.Vec.Insts.ArbitraryArbitrary.arbitrary
  congr 1
  funext result
  rcases result with ⟨generated, after⟩
  cases generated with
  | Err error => rfl
  | Ok values =>
    simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    congr 1
    funext built
    cases built <;> rfl

/-- Successful generation is exactly a successful vector followed by the
actual successful constructor. No input-consumption or trait laws are needed. -/
theorem ProgressiveList.arbitrary_success_iff {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U) :
    ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after) ↔
    ∃ values, arbitrary.vector inst input = ok (.Ok values, after) ∧
      ProgressiveList.new ValueInst mapInst values = ok (.Ok self) := by
  rw [ProgressiveList.arbitrary_eq]
  constructor
  · intro hresult
    rw [builder.bind_eq_ok_iff] at hresult
    obtain ⟨⟨generated, remaining⟩, hvector, hresult⟩ := hresult
    simp! only at hresult
    cases generated with
    | Err error => simp at hresult
    | Ok values =>
      rw [builder.bind_eq_ok_iff] at hresult
      obtain ⟨built, hnew, hresult⟩ := hresult
      cases built with
      | Err error => simp at hresult
      | Ok output =>
        simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hresult
        rcases hresult with ⟨rfl, rfl⟩
        exact ⟨values, hvector, hnew⟩
  · rintro ⟨values, hvector, hnew⟩
    simp! only [hvector, hnew, bind_tc_ok]

/-- The vector's first element error is returned unchanged with its final
input state; construction is never called on this branch. -/
theorem ProgressiveList.arbitrary_of_vector_error {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (error : arbitrary.error.Error)
    (hvector : arbitrary.vector inst input = ok (.Err error, after)) :
    ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Err error, after) := by
  rw [ProgressiveList.arbitrary_eq]
  simp! only [hvector, bind_tc_ok]

/-- A constructor error is mapped only after the whole vector has been
generated. Its consumed input is retained even when construction rejects it. -/
theorem ProgressiveList.arbitrary_of_constructor_error {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T)
    (error : milhouse.error.Error)
    (hvector : arbitrary.vector inst input = ok (.Ok values, after))
    (hnew : ProgressiveList.new ValueInst mapInst values = ok (.Err error)) :
    ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Err arbitrary.error.Error.IncorrectFormat, after) := by
  rw [ProgressiveList.arbitrary_eq]
  simp! only [hvector, hnew, bind_tc_ok]

/-- Every generated list has the exact generated backing values and recorded
length and the actual default update map. No packing or map laws are needed. -/
theorem ProgressiveList.arbitrary_contents {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) :
    ∃ values, arbitrary.vector inst input = ok (.Ok values, after) ∧
      self.tree.elements = values.val ∧ self.length.val = values.val.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  obtain ⟨values, hvector, hnew⟩ :=
    (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
  exact ⟨values, hvector, ProgressiveList.new_contents ValueInst mapInst values hnew⟩

/-- Successful generation establishes dense, representable backing layers.
This holds for every element generator and default map, including ones that
do not satisfy the stronger empty-map representation laws. -/
theorem ProgressiveList.arbitrary_backing_valid {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) : self.BackingValid factor := by
  obtain ⟨values, _, hnew⟩ :=
    (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
  exact ProgressiveList.new_backing_valid ValueInst mapInst hlayout values hnew

end milhouse.progressive_list
