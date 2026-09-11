import Tree.ProgressiveList.PopFront.BuilderLength
import Tree.ProgressiveTree.Builder.PushLength

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Streaming the represented iterator into a valid builder terminates.
Only clones of yielded values must terminate; their results may differ from
the input values. The final occupied
capacities supply every insertion and rollover bound. -/
theorem ProgressiveListIter.extend_builder_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) self values)
    (hclone : ∀ value ∈ values, ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
    {factor : Option Std.Usize} (hvalid : initial.Valid ValueInst factor)
    (hfits : ProgressiveTree.LengthFits factor (initial.length.val + values.length)) :
    ∃ result, ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result) := by
  change ∃ result, ProgressiveListIter.extend_builder_loop ValueInst mapInst initial self =
    ok (core.result.Result.Ok (), result)
  induction hyields generalizing initial with
  | nil hnext =>
    refine ⟨initial, ?_⟩
    rw [ProgressiveListIter.extend_builder_loop, loop]
    simp! only [ProgressiveListIter.extend_builder_loop.body, hnext, bind_tc_ok]
  | @cons self rest value values hnext hyields ih =>
    obtain ⟨cloned, hcloned⟩ := hclone value (by simp)
    obtain ⟨pushed, hpush, hvalidPushed, _, hlength⟩ :=
      ProgressiveTreeBuilder.push_length_fits_spec ValueInst initial hvalid
        (hfits.mono (by simp only [_root_.List.length_cons]; omega)) cloned
    have hfitsPushed : ProgressiveTree.LengthFits factor (pushed.length.val + values.length) := by
      simpa only [hlength, _root_.List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hfits
    obtain ⟨result, hresult⟩ := ih pushed (fun value hv => hclone value (by simp [hv]))
      hvalidPushed hfitsPushed
    refine ⟨result, ?_⟩
    rw [ProgressiveListIter.extend_builder_loop, loop]
    simp! only [ProgressiveListIter.extend_builder_loop.body, hnext, hcloned,
      hpush, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    exact hresult

/-- Total streaming reconstruction appends exactly the cursor's values,
records their count once, and retains the complete builder invariant. -/
theorem ProgressiveListIter.extend_builder_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) self values)
    (hclone : ∀ value ∈ values, ValueInst.corecloneCloneInst.clone value = ok value)
    {factor : Option Std.Usize} (hvalid : initial.Valid ValueInst factor)
    (hfits : ProgressiveTree.LengthFits factor (initial.length.val + values.length)) :
    ∃ result, ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result) ∧ result.Valid ValueInst factor ∧
      result.elements = initial.elements ++ values ∧
      result.length.val = initial.length.val + values.length := by
  obtain ⟨result, hextend⟩ := ProgressiveListIter.extend_builder_success ValueInst mapInst
    self initial values hyields (fun value hv => ⟨value, hclone value hv⟩) hvalid hfits
  obtain ⟨helements, hlength⟩ := ProgressiveListIter.extend_builder_contents ValueInst mapInst
    self initial values hyields hclone hextend
  exact ⟨result, hextend, ProgressiveListIter.extend_builder_preserves_valid ValueInst mapInst
    self initial hvalid hextend, helements, hlength⟩

end milhouse.progressive_list
