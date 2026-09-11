import Tree.ProgressiveTree.Builder.Iterator
import Tree.ProgressiveTree.Builder.Finish

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Successful construction stores exactly the values yielded by the input
    iterator, and returns their exact length. Builder counters are established
    internally; no representation, packing, or cloning premise is required. -/
theorem ProgressiveTree.build_from_iter_with_len_elements {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {output : ProgressiveTree T} {length : Std.Usize}
    (hbuild : ProgressiveTree.build_from_iter_with_len ValueInst iterInst input =
      ok (core.result.Result.Ok (output, length))) :
    output.elements = values ∧ length.val = values.length := by
  obtain ⟨iter, hiter, hyields⟩ := hyields
  unfold ProgressiveTree.build_from_iter_with_len at hbuild
  rw [bind_eq_ok_iff] at hbuild
  obtain ⟨status, hnew, hbuild⟩ := hbuild
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
  | Ok initial =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, hiter, bind_tc_ok] at hbuild
    rw [bind_eq_ok_iff] at hbuild
    obtain ⟨⟨status, built⟩, hextend, hbuild⟩ := hbuild
    dsimp! only at hbuild
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
    | Ok success =>
      cases success
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hbuild
      obtain ⟨hempty, hcounts⟩ := ProgressiveTreeBuilder.new_elements ValueInst hnew
      obtain ⟨helements, _, hpreserves⟩ := ProgressiveTreeBuilder.extend_from_iter_elements
        ValueInst iterInst.iteratorInst initial iter values hyields hextend
      have hbuiltCounts := hpreserves hcounts
      obtain ⟨houtput, rfl⟩ := ProgressiveTreeBuilder.finish_elements ValueInst built hbuiltCounts.1 hbuild
      have hbuilt : built.elements = values := by simpa [hempty] using helements
      exact ⟨houtput.trans hbuilt, hbuiltCounts.2.trans (congrArg _root_.List.length hbuilt)⟩

theorem ProgressiveTree.build_from_iter_elements {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {output : ProgressiveTree T}
    (hbuild : ProgressiveTree.build_from_iter ValueInst iterInst input =
      ok (core.result.Result.Ok output)) :
    output.elements = values := by
  unfold ProgressiveTree.build_from_iter at hbuild
  rw [bind_eq_ok_iff] at hbuild
  obtain ⟨status, hinner, hbuild⟩ := hbuild
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
  | Ok result =>
    obtain ⟨built, length⟩ := result
    simp! [core.result.Result.Insts.CoreOpsTry.branch] at hbuild
    subst output
    exact (ProgressiveTree.build_from_iter_with_len_elements ValueInst iterInst input values hyields hinner).1

/-- Any successful construction establishes a dense spine and representable
    binary layers. No separate iterator finiteness or input-sequence premise is
    needed for this structural result. -/
theorem ProgressiveTree.build_from_iter_with_len_valid {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {output : ProgressiveTree T} {length : Std.Usize}
    (hbuild : ProgressiveTree.build_from_iter_with_len ValueInst iterInst input =
      ok (core.result.Result.Ok (output, length))) :
    output.Dense factor 0 length.val ∧ output.Fits factor 0 := by
  unfold ProgressiveTree.build_from_iter_with_len at hbuild
  rw [bind_eq_ok_iff] at hbuild
  obtain ⟨status, hnew, hbuild⟩ := hbuild
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
  | Ok initial =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hbuild
    rw [bind_eq_ok_iff] at hbuild
    obtain ⟨iter, _, hbuild⟩ := hbuild
    rw [bind_eq_ok_iff] at hbuild
    obtain ⟨⟨status, built⟩, hextend, hbuild⟩ := hbuild
    dsimp! only at hbuild
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
    | Ok success =>
      cases success
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hbuild
      have hinitial := ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew
      have hbuilt := ProgressiveTreeBuilder.extend_from_iter_preserves_valid
        ValueInst iterInst.iteratorInst initial iter hinitial hextend
      exact (ProgressiveTreeBuilder.finish_spec ValueInst built hbuilt hbuild).2.2

end milhouse.progressive_tree
