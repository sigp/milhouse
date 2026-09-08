import Tree.ProgressiveTree.Builder.Finish

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list.Decode

/-- The common finalization expression in both exits of the extracted decode
loop. This factors the proof only; each use is definitionally equal to the
actual extracted loop body after the relevant next/decode result. -/
def finishBody {T U : Type} (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (builder : ProgressiveTreeBuilder T) (decodeError : Option ssz.decode.DecodeError) :
    Result (ControlFlow (ssz_items.SszItems × ProgressiveTreeBuilder T)
      (core.result.Result (ProgressiveList T U) error.Error × Option ssz.decode.DecodeError)) := do
  let result ← ProgressiveTreeBuilder.finish ValueInst builder
  match result with
  | .Ok pair =>
    let (tree, length) := pair
    let tree ← triomphe.arc.Arc.new tree
    let updates ← mapInst.coredefaultDefaultInst.default
    ok (.done (.Ok { tree, length, updates }, decodeError))
  | .Err error => ok (.done (.Err error, decodeError))

/-- Finalization exits the loop and retains the decode error exactly. A
returned list comes from the actual builder finish and default-map calls. -/
theorem finishBody_outcome {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (builder : ProgressiveTreeBuilder T) (decodeError : Option ssz.decode.DecodeError)
    {flow} (hbody : finishBody ValueInst mapInst builder decodeError = ok flow) :
    ∃ status, flow = .done (status, decodeError) ∧
      ∀ self, status = core.result.Result.Ok self →
        ProgressiveTreeBuilder.finish ValueInst builder =
          ok (core.result.Result.Ok (self.tree, self.length)) ∧
        mapInst.coredefaultDefaultInst.default = ok self.updates := by
  unfold finishBody at hbody
  rw [bind_eq_ok_iff] at hbody
  obtain ⟨status, hfinish, hbody⟩ := hbody
  cases status with
  | Err e =>
    simp only [ok.injEq] at hbody
    exact ⟨.Err e, hbody.symm, by simp⟩
  | Ok pair =>
    obtain ⟨tree, length⟩ := pair
    simp! only [triomphe.arc.Arc.new, bind_tc_ok, bind_eq_ok_iff] at hbody
    obtain ⟨updates, hdefault, hbody⟩ := hbody
    simp only [ok.injEq] at hbody
    refine ⟨.Ok { tree, length, updates }, hbody.symm, ?_⟩
    intro self hself
    cases hself
    exact ⟨hfinish, hdefault⟩

theorem finishBody_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (builder : ProgressiveTreeBuilder T) (decodeError : Option ssz.decode.DecodeError)
    {self : ProgressiveList T U} {reportedError : Option ssz.decode.DecodeError}
    (hbody : finishBody ValueInst mapInst builder decodeError =
      ok (.done (core.result.Result.Ok self, reportedError))) :
    ProgressiveTreeBuilder.finish ValueInst builder =
      ok (core.result.Result.Ok (self.tree, self.length)) ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates ∧
      reportedError = decodeError := by
  obtain ⟨status, heq, houtcome⟩ := finishBody_outcome ValueInst mapInst builder decodeError hbody
  cases heq
  exact ⟨(houtcome self rfl).1, (houtcome self rfl).2, rfl⟩

/-- When the actual next step is a finalization exit, a successful loop result
is exactly the result of that exit. No assumptions about other steps or loop
termination are needed. -/
theorem loop_finishes {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (builder : ProgressiveTreeBuilder T)
    (decodeError : Option ssz.decode.DecodeError)
    (hbody : ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst items builder =
      finishBody ValueInst mapInst builder decodeError)
    {result} (hloop : ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder = ok result) :
    finishBody ValueInst mapInst builder decodeError = ok (.done result) := by
  rw [ProgressiveList.decode_ssz_items_loop, loop] at hloop
  simp! only [hbody] at hloop
  cases hfinish : finishBody ValueInst mapInst builder decodeError with
  | fail e => simp [hfinish] at hloop
  | div => simp [hfinish] at hloop
  | ok flow =>
    obtain ⟨status, rfl, _⟩ := finishBody_outcome ValueInst mapInst builder decodeError hfinish
    simp only [hfinish, bind_tc_ok, ok.injEq] at hloop
    cases hloop
    rfl

end milhouse.progressive_list.Decode
