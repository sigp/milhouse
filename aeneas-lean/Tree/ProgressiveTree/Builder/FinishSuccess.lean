import Tree.Builder.Finish.Success
import Tree.ProgressiveTree.Builder.SpineSuccess
import Tree.ProgressiveTree.Builder.Finish

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- Progressive finalization succeeds from its builder geometry alone. The
counter agreement laws are needed for content correctness, not for success. -/
theorem ProgressiveTreeBuilder.finish_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T)
    (hgeometry : self.Geometry ValueInst factor) :
    ∃ output, ProgressiveTreeBuilder.finish ValueInst self =
      ok (core.result.Result.Ok (output, self.length)) := by
  by_cases hcount : self.count > 0#usize
  · obtain ⟨hcurrent, _, _, hdepth, _, _, _⟩ := hgeometry
    obtain ⟨tree, hfinish⟩ := Builder.finish_success self.current hcurrent
    have hroom : self.subtrees.val.length < Std.Usize.max := by
      have hdepthMax : self.current.depth.val ≤ Std.Usize.max := by scalar_tac
      have hpositive : 0 < Std.Usize.max := by scalar_tac
      omega
    obtain ⟨subtrees, hpush, _⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec self.subtrees tree hroom)
    refine ⟨ProgressiveTree.ofSubtrees subtrees.val .ProgressiveZero, ?_⟩
    simp! only [ProgressiveTreeBuilder.finish, hcount, ↓reduceIte, hfinish, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch, hpush, ProgressiveTree.from_spine_subtrees_success]
  · refine ⟨ProgressiveTree.ofSubtrees self.subtrees.val .ProgressiveZero, ?_⟩
    simp only [ProgressiveTreeBuilder.finish, hcount, ↓reduceIte,
      ProgressiveTree.from_spine_subtrees_success, bind_tc_ok]

/-- Every valid progressive builder finishes with exactly its complete value
sequence and recorded length, a dense spine, and representable lookup layers.
No arithmetic, cloning, or successful-subcall assumptions are added. -/
theorem ProgressiveTreeBuilder.finish_total_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T)
    (hvalid : self.Valid ValueInst factor) :
    ∃ output, ProgressiveTreeBuilder.finish ValueInst self =
      ok (core.result.Result.Ok (output, self.length)) ∧ output.elements = self.elements ∧
      output.Dense factor 0 self.length.val ∧ output.Fits factor 0 := by
  obtain ⟨output, hfinish⟩ := ProgressiveTreeBuilder.finish_success ValueInst self hvalid.1
  obtain ⟨helements, _, hdense, hfits⟩ := ProgressiveTreeBuilder.finish_spec ValueInst self hvalid hfinish
  exact ⟨output, hfinish, helements, hdense, hfits⟩

end milhouse.progressive_tree
