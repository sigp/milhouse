import Tree.Iterator
import Tree.ProgressiveTree.Builder.Contents

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_tree

/-- Consuming a finite iterator appends its yielded sequence and preserves the
    counter invariant. The premise describes actual `next` calls, rather than
    assuming any property of the builder's result. -/
theorem ProgressiveTreeBuilder.extend_from_iter_elements {T I : Type}
    (ValueInst : Value T) (iterInst : core.iter.traits.iterator.Iterator I T)
    (self : ProgressiveTreeBuilder T) (iter : I) (values : _root_.List T)
    (hyields : IteratorYields iterInst.next iter values)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveTreeBuilder.extend_from_iter ValueInst iterInst self iter =
      ok (core.result.Result.Ok (), result)) :
    result.elements = self.elements ++ values ∧
      result.length.val = self.length.val + values.length ∧
      (self.Counts → result.Counts) := by
  change ProgressiveTreeBuilder.extend_from_iter_loop ValueInst iterInst iter self =
    ok (core.result.Result.Ok (), result) at hextend
  induction hyields generalizing self with
  | nil hnext =>
    rw [ProgressiveTreeBuilder.extend_from_iter_loop, loop] at hextend
    simp! only [ProgressiveTreeBuilder.extend_from_iter_loop.body, hnext, bind_tc_ok] at hextend
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hextend
    subst result
    simp
  | @cons iter rest value values hnext hyields ih =>
    rw [ProgressiveTreeBuilder.extend_from_iter_loop, loop] at hextend
    simp! only [ProgressiveTreeBuilder.extend_from_iter_loop.body, hnext, bind_tc_ok] at hextend
    cases hpush : ProgressiveTreeBuilder.push ValueInst self value with
    | fail e => simp [hpush, Bind.bind, Std.bind] at hextend
    | div => simp [hpush, Bind.bind, Std.bind] at hextend
    | ok pair =>
      obtain ⟨status, pushed⟩ := pair
      cases status with
      | Err e =>
        simp! [hpush, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          Bind.bind, Std.bind] at hextend
      | Ok success =>
        cases success
        simp! only [hpush, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at hextend
        obtain ⟨helements, hlength, hcounts⟩ := ih pushed hextend
        obtain ⟨happended, hincrement, _⟩ := ProgressiveTreeBuilder.push_contents ValueInst self value hpush
        refine ⟨?_, ?_, fun h => hcounts (ProgressiveTreeBuilder.push_preserves_counts
          ValueInst self value h hpush)⟩
        · simpa [happended, _root_.List.append_assoc] using helements
        · simpa [hincrement, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength

end milhouse.progressive_tree
