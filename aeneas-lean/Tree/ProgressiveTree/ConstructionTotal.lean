import Tree.ProgressiveTree.Construction
import Tree.ProgressiveTree.Builder.New
import Tree.ProgressiveTree.Builder.ExtendSuccess
import Tree.ProgressiveTree.Builder.FinishSuccess

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Progressive construction from a finite iterator succeeds and returns its
exact sequence and length, with dense backing and representable layers. The
final occupied-layer bound supplies all intermediate builder checks. -/
theorem ProgressiveTree.build_from_iter_with_len_total_spec {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length) :
    ∃ output length, ProgressiveTree.build_from_iter_with_len ValueInst iterInst input =
      ok (core.result.Result.Ok (output, length)) ∧ output.elements = values ∧
      length.val = values.length ∧ output.Dense factor 0 length.val ∧ output.Fits factor 0 := by
  obtain ⟨iter, hiter, hyields⟩ := hyields
  obtain ⟨initial, hnew, hvalid, hempty, hzero⟩ := ProgressiveTreeBuilder.new_spec ValueInst hlayout
  obtain ⟨built, hextend, hvalidBuilt, hbuilt, hlength⟩ :=
    ProgressiveTreeBuilder.extend_from_iter_total_spec ValueInst iterInst.iteratorInst initial iter
      values hyields hvalid (by simpa only [hzero, Nat.zero_add] using hfits)
  obtain ⟨output, hfinish, helements, hdense, hfits⟩ :=
    ProgressiveTreeBuilder.finish_total_spec ValueInst built hvalidBuilt
  refine ⟨output, built.length, ?_, ?_, ?_, hdense, hfits⟩
  · simp! only [ProgressiveTree.build_from_iter_with_len, hnew,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, hiter, hextend, hfinish]
  · simpa only [hbuilt, hempty, _root_.List.nil_append] using helements
  · simpa only [hzero, Nat.zero_add] using hlength

/-- The tree-only constructor also succeeds, retaining the complete sequence
and the density/capacity invariants needed for indexed access. -/
theorem ProgressiveTree.build_from_iter_total_spec {T Input I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length) :
    ∃ output, ProgressiveTree.build_from_iter ValueInst iterInst input =
      ok (core.result.Result.Ok output) ∧ output.elements = values ∧
      output.Dense factor 0 values.length ∧ output.Fits factor 0 := by
  obtain ⟨output, length, hbuild, helements, hlength, hdense, hfits⟩ :=
    ProgressiveTree.build_from_iter_with_len_total_spec ValueInst iterInst input values hyields
      hlayout hfits
  refine ⟨output, ?_, helements, ?_, hfits⟩
  · simp! only [ProgressiveTree.build_from_iter, hbuild, core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok]
  · simpa only [hlength] using hdense

end milhouse.progressive_tree
