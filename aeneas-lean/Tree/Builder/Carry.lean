import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.tree

/-- Each canonical stack entry contains at least one logical value. -/
theorem BuilderStack.entries_le_length {T : Type} {factor : Option Std.Usize}
    {base depth len : Nat} {stack : _root_.List (utils.MaybeArced (Tree T))}
    (hstack : BuilderStack factor base stack depth len) : stack.length ≤ len := by
  induction hstack with
  | empty => simp
  | base entry len hdense hpositive => simp; omega
  | full entry depth hbase hdense hpositive => simp; omega
  | segment entry depth len hbase hdense hpositive hfinal => simp; omega
  | left _ _ ih => exact ih
  | right entry depth len hdense htail hpositive hpartial ih =>
    simp only [_root_.List.length_cons]
    omega

/-- Carry merging only removes entries from the pending forest. -/
theorem BuilderMergePlan.final_stack_length_le {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {count depth len : Nat}
    {stack finalStack : _root_.List (utils.MaybeArced (Tree T))} {top finalTop : Tree T}
    (hplan : BuilderMergePlan ValueInst factor count stack top finalStack finalTop depth len) :
    finalStack.length ≤ stack.length := by
  induction hplan with
  | done => rfl
  | step _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [_root_.List.length_append, _root_.List.length_singleton]
    omega

end milhouse.tree

namespace milhouse.builder

/-- Every merge prescribed by the canonical stack terminates successfully,
then stores the final subtree and increments the logical length once. -/
theorem Builder.push_loop0_success {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {count depth len : Nat}
    {input finalStack : _root_.List (utils.MaybeArced (tree.Tree T))}
    {top finalTop : tree.Tree T}
    (hplan : BuilderMergePlan ValueInst factor count input top finalStack finalTop depth len)
    (iter : core.ops.range.Range Std.U32)
    (stack : alloc.vec.Vec (utils.MaybeArced (tree.Tree T))) (length : Std.Usize)
    (hremaining : iter.end.val = iter.start.val + count) (hstack : stack.val = input)
    (hroom : input.length < Std.Usize.max) (hlength : length.val < Std.Usize.max) :
    ∃ resultStack resultLength,
      Builder.push_loop0 ValueInst iter stack length top =
        ok (core.result.Result.Ok (), resultStack, resultLength) ∧
      resultStack.val = finalStack ++ [utils.MaybeArced.Unarced finalTop] ∧
      resultLength.val = length.val + 1 := by
  induction hplan generalizing iter stack with
  | done input top depth len hdense hpositive =>
    have hnext := range_u32_next_none iter (by omega)
    obtain ⟨resultStack, hpush, hvalues⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec stack (utils.MaybeArced.Unarced top) (by simpa only [hstack] using hroom))
    have hbound : length.val + (1#usize).val ≤ UScalar.max .Usize := by
      rw [UScalar.max_USize_eq]
      change length.val + 1 ≤ Std.Usize.max
      omega
    obtain ⟨resultLength, hadd, hval⟩ := WP.spec_imp_exists (UScalar.add_spec hbound)
    refine ⟨resultStack, resultLength, ?_, ?_, hval⟩
    · rw [push_loop0_step]
      simp! only [Builder.push_loop0.body, hnext, bind_tc_ok, hpush,
        utils.Length.as_mut, hadd]
    · simpa only [hstack] using hvalues
  | @step input left top merged depth len count finalStack finalTop finalDepth finalLen
      hleft htop hpositive hmerge hplan ih =>
    obtain ⟨iter1, hnext, hstart, hend⟩ := range_u32_next_some iter (by omega)
    obtain ⟨rest, hpop, hrest⟩ := vec_pop_append_last (A := Global) stack input left hstack
    obtain ⟨resultStack, resultLength, hloop, hvalues, hval⟩ := ih iter1 rest
      (by have := congrArg UScalar.val hend; omega) hrest
      (by simp only [_root_.List.length_append, _root_.List.length_singleton] at hroom; omega)
    refine ⟨resultStack, resultLength, ?_, hvalues, hval⟩
    rw [push_loop0_step]
    simp! only [Builder.push_loop0.body, hnext, hpop, bind_tc_ok, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, maybeArced_arced,
      maybeArcedTree_unarced, triomphe.arc.Arc.new, hmerge]
    exact hloop

end milhouse.builder
