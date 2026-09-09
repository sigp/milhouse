import Tree.ProgressiveTree.Construction
import Tree.ProgressiveTree.Builder.Trace

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Every successful progressive-tree construction consumed exactly the
materialized sequence through the iterator's first none and returned its
length. Iterator finiteness and values follow from the actual builder loop;
no iterator, packing, cloning, or initial-invariant premise is assumed. -/
theorem ProgressiveTree.build_from_iter_with_len_trace {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) {output : ProgressiveTree T} {length : Std.Usize}
    (hbuild : ProgressiveTree.build_from_iter_with_len ValueInst iterInst input =
      ok (core.result.Result.Ok (output, length))) :
    IntoIteratorYields iterInst input output.elements ∧ length.val = output.elements.length := by
  have hyields : ∃ values, IntoIteratorYields iterInst input values := by
    unfold ProgressiveTree.build_from_iter_with_len at hbuild
    rw [bind_eq_ok_iff] at hbuild
    obtain ⟨status, _, hbuild⟩ := hbuild
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
    | Ok initial =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hbuild
      rw [bind_eq_ok_iff] at hbuild
      obtain ⟨iter, hiter, hbuild⟩ := hbuild
      rw [bind_eq_ok_iff] at hbuild
      obtain ⟨⟨status, built⟩, hextend, hbuild⟩ := hbuild
      dsimp! only at hbuild
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbuild
      | Ok success =>
        cases success
        obtain ⟨values, hyields, _⟩ := ProgressiveTreeBuilder.extend_from_iter_trace
          ValueInst iterInst.iteratorInst initial iter hextend
        exact ⟨values, iter, hiter, hyields⟩
  obtain ⟨values, hyields⟩ := hyields
  obtain ⟨helements, hlength⟩ := ProgressiveTree.build_from_iter_with_len_elements
    ValueInst iterInst input values hyields hbuild
  simpa only [helements] using And.intro hyields hlength

end milhouse.progressive_tree
