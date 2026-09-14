import Tree.ProgressiveTree.Builder.Caches.Iterator

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Every successful iterator construction initializes all stored caches to
zero. No element-hashing, packing, iterator-output, or finiteness premise is
needed for this initialization property. -/
theorem ProgressiveTree.build_from_iter_with_len_caches_cleared {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input)
    {output : ProgressiveTree T} {length : Std.Usize}
    (hbuild : ProgressiveTree.build_from_iter_with_len ValueInst iterInst input =
      ok (core.result.Result.Ok (output, length))) :
    output.CachesCleared := by
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
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
    | Ok success =>
      cases success
      simp only [bind_tc_ok] at hbuild
      have hinitial := ProgressiveTreeBuilder.new_caches_cleared ValueInst hnew
      have hbuilt := ProgressiveTreeBuilder.extend_from_iter_preserves_cleared_caches
        ValueInst iterInst.iteratorInst initial iter hinitial hextend
      exact ProgressiveTreeBuilder.finish_caches_cleared ValueInst built hbuilt hbuild

theorem ProgressiveTree.build_from_iter_caches_cleared {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input)
    {output : ProgressiveTree T}
    (hbuild : ProgressiveTree.build_from_iter ValueInst iterInst input =
      ok (core.result.Result.Ok output)) :
    output.CachesCleared := by
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
    exact ProgressiveTree.build_from_iter_with_len_caches_cleared ValueInst iterInst input hinner

end milhouse.progressive_tree
