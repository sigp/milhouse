import Tree.ProgressiveList.Iter.Construction
import Tree.ProgressiveTree.Builder.Finish
import Tree.Loop
import Tree.Vec.Clone

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful streaming reconstruction stores the actual ordered clone
results and counts every yielded value once. Execution itself supplies clone
termination; no clone identity, builder invariant, or capacity law is assumed. -/
theorem ProgressiveListIter.extend_builder_clones {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) self values)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result)) :
    ∃ copied, _root_.List.mapM ValueInst.corecloneCloneInst.clone values = ok copied ∧
      result.elements = initial.elements ++ copied ∧
      result.length.val = initial.length.val + values.length := by
  change ProgressiveListIter.extend_builder_loop ValueInst mapInst initial self =
    ok (core.result.Result.Ok (), result) at hextend
  induction hyields generalizing initial with
  | nil hnext =>
    rw [ProgressiveListIter.extend_builder_loop, loop] at hextend
    simp! only [ProgressiveListIter.extend_builder_loop.body, hnext, bind_tc_ok] at hextend
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hextend
    subst result
    exact ⟨[], rfl, by simp, by simp⟩
  | @cons self rest value values hnext hyields ih =>
    rw [ProgressiveListIter.extend_builder_loop, loop] at hextend
    simp! only [ProgressiveListIter.extend_builder_loop.body, hnext, bind_tc_ok] at hextend
    cases hclone : ValueInst.corecloneCloneInst.clone value with
    | fail e => simp [hclone, Bind.bind, Std.bind] at hextend
    | div => simp [hclone, Bind.bind, Std.bind] at hextend
    | ok cloned =>
      simp only [hclone, bind_tc_ok] at hextend
      cases hpush : ProgressiveTreeBuilder.push ValueInst initial cloned with
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
          obtain ⟨copied, hcopied, helements, hlength⟩ := ih pushed hextend
          obtain ⟨happended, hincrement, _⟩ := ProgressiveTreeBuilder.push_contents ValueInst initial cloned hpush
          refine ⟨cloned :: copied, ?_, ?_, ?_⟩
          · simp only [_root_.List.mapM_cons, hclone, hcopied, Pure.pure, bind_tc_ok]
          · simpa only [happended, _root_.List.append_assoc, _root_.List.cons_append,
              _root_.List.nil_append] using helements
          · simpa only [hincrement, _root_.List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hlength

end milhouse.progressive_list
