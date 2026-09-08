import Tree.ProgressiveTree.Builder.Invariant

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

private theorem assembled_fits {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {self : ProgressiveTreeBuilder T}
    (hgeometry : self.Geometry ValueInst factor)
    {subtrees : alloc.vec.Vec (tree.Tree T)} {output : ProgressiveTree T}
    (hcount : subtrees.val.length ≤ self.subtrees.val.length + 1)
    (hassemble : ProgressiveTree.from_spine_subtrees ValueInst subtrees = ok output) :
    output.Fits factor 0 := by
  obtain ⟨hcurrent, hfactor, _, hdepth, _, _, _⟩ := hgeometry
  have hcapacity := @BuilderInvariant.builder_capacity_matches T ValueInst self.current hcurrent
  rw [hfactor, hdepth] at hcapacity
  have hfit : subtreeCapacity factor (2 * self.subtrees.val.length) < 2 ^ System.Platform.numBits := by
    rw [← hcapacity]
    scalar_tac
  apply ProgressiveTree.from_spine_subtrees_fits ValueInst ?_ hassemble
  intro i hi
  exact lt_of_le_of_lt (subtreeCapacity_mono_depth factor (by omega)) hfit

/-- A valid progressive builder finishes with exactly its accumulated values,
    a dense spine, and representable lookup layers. Every machine bound follows
    from the current binary builder and the ordering of the completed layers. -/
theorem ProgressiveTreeBuilder.finish_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T)
    (hvalid : self.Valid ValueInst factor) {output : ProgressiveTree T} {length : Std.Usize}
    (hfinish : ProgressiveTreeBuilder.finish ValueInst self =
      ok (core.result.Result.Ok (output, length))) :
    output.elements = self.elements ∧ length = self.length ∧
      output.Dense factor 0 length.val ∧ output.Fits factor 0 := by
  obtain ⟨hgeometry, hcounts⟩ := hvalid
  obtain ⟨helements, hlength⟩ := ProgressiveTreeBuilder.finish_elements ValueInst self hcounts.1 hfinish
  refine ⟨helements, hlength, ?_⟩
  have hlengthVal : length.val = self.elements.length := by rw [hlength]; exact hcounts.2
  rw [hlengthVal]
  unfold ProgressiveTreeBuilder.finish at hfinish
  split at hfinish
  · rw [bind_eq_ok_iff] at hfinish
    obtain ⟨status, hcurrent, hfinish⟩ := hfinish
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hfinish
    | Ok result =>
      obtain ⟨current, depth, currentLength⟩ := result
      simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨subtrees, hsubtrees, hfinish⟩ := hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨assembled, hassemble, hfinish⟩ := hfinish
      simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
      obtain ⟨rfl, _⟩ := hfinish
      refine ⟨?_, assembled_fits ValueInst hgeometry (by simp [vec_push_values hsubtrees]) hassemble⟩
      obtain ⟨hcurrentValid, hfactor, _, hdepth, _, _, hfull⟩ := hgeometry
      obtain ⟨_, hresultDepth, _, hdense⟩ := Builder.finish_spec hcurrentValid hcurrent
      rw [hresultDepth, hfactor, hdepth] at hdense
      have hassembled := ProgressiveTree.from_spine_subtrees_dense_last ValueInst
        (vec_push_values hsubtrees) hfull hdense hassemble
      simpa [ProgressiveTreeBuilder.elements] using hassembled
  · rename_i hzero
    rw [bind_eq_ok_iff] at hfinish
    obtain ⟨assembled, hassemble, hfinish⟩ := hfinish
    simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
    obtain ⟨rfl, _⟩ := hfinish
    refine ⟨?_, assembled_fits ValueInst hgeometry (by omega) hassemble⟩
    have hempty : self.current.elements = [] := by
      apply _root_.List.length_eq_zero_iff.mp
      have : self.count.val = 0 := by
        have hnonpos : ¬ (0 : Nat) < self.count.val := hzero
        omega
      have := hcounts.1
      omega
    obtain ⟨_, _, _, _, _, _, hfull⟩ := hgeometry
    rw [ProgressiveTree.from_spine_subtrees_eq ValueInst self.subtrees hassemble]
    have hdense := ProgressiveTree.ofSubtrees_dense self.subtrees.val .ProgressiveZero hfull
      (ProgressiveTree.Dense.zero factor (0 + self.subtrees.val.length))
    simpa [ProgressiveTreeBuilder.elements, hempty] using hdense

end milhouse.progressive_tree
