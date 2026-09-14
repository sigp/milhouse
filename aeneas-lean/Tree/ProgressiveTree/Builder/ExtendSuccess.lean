import Tree.ProgressiveTree.Builder.Iterator
import Tree.ProgressiveTree.Builder.PushLength

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Extending a valid progressive builder consumes a finite iterator and
terminates successfully when the occupied layers of the final sequence fit.
All intermediate counters and rollover bounds follow from that final bound. -/
theorem ProgressiveTreeBuilder.extend_from_iter_success {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    (self : ProgressiveTreeBuilder T) (iter : I) (values : _root_.List T)
    (hyields : IteratorYields iterInst.next iter values)
    {factor : Option Std.Usize} (hvalid : self.Valid ValueInst factor)
    (hfits : ProgressiveTree.LengthFits factor (self.length.val + values.length)) :
    ∃ result, ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result) := by
  change ∃ result, ProgressiveTreeBuilder.extend_from_iter_loop ValueInst iterInst iter self =
    ok (core.result.Result.Ok (), result)
  induction hyields generalizing self with
  | nil hnext =>
    refine ⟨self, ?_⟩
    rw [ProgressiveTreeBuilder.extend_from_iter_loop, loop]
    simp! only [ProgressiveTreeBuilder.extend_from_iter_loop.body, hnext, bind_tc_ok]
  | @cons iter rest value values hnext hyields ih =>
    obtain ⟨pushed, hpush, hvalidPushed, _, hlength⟩ :=
      ProgressiveTreeBuilder.push_length_fits_spec ValueInst self hvalid
        (hfits.mono (by simp only [_root_.List.length_cons]; omega)) value
    have hfitsPushed : ProgressiveTree.LengthFits factor (pushed.length.val + values.length) := by
      simpa only [hlength, _root_.List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hfits
    obtain ⟨result, hresult⟩ := ih pushed hvalidPushed hfitsPushed
    refine ⟨result, ?_⟩
    rw [ProgressiveTreeBuilder.extend_from_iter_loop, loop]
    simp! only [ProgressiveTreeBuilder.extend_from_iter_loop.body, hnext, hpush,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    exact hresult

/-- Total iterator extension appends exactly the yielded values, increases
the recorded length by their count, and preserves the complete builder
invariant. No successful builder or loop call is assumed. -/
theorem ProgressiveTreeBuilder.extend_from_iter_total_spec {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    (self : ProgressiveTreeBuilder T) (iter : I) (values : _root_.List T)
    (hyields : IteratorYields iterInst.next iter values)
    {factor : Option Std.Usize} (hvalid : self.Valid ValueInst factor)
    (hfits : ProgressiveTree.LengthFits factor (self.length.val + values.length)) :
    ∃ result, ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result) ∧ result.Valid ValueInst factor ∧
      result.elements = self.elements ++ values ∧
      result.length.val = self.length.val + values.length := by
  obtain ⟨result, hextend⟩ := ProgressiveTreeBuilder.extend_from_iter_success ValueInst iterInst
    self iter values hyields hvalid hfits
  obtain ⟨helements, hlength, _⟩ := ProgressiveTreeBuilder.extend_from_iter_elements
    ValueInst iterInst self iter values hyields hextend
  exact ⟨result, hextend, ProgressiveTreeBuilder.extend_from_iter_preserves_valid
    ValueInst iterInst self iter hvalid hextend, helements, hlength⟩

end milhouse.progressive_tree
