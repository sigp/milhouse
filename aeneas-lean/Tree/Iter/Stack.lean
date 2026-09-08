import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.builder

namespace milhouse.iter

/-- Popping the traversal stack succeeds even when it is empty, and removes
    precisely its last entry when one exists. -/
theorem vec_pop_spec {T : Type} (stack : alloc.vec.Vec T) :
    ∃ entry rest, alloc.vec.Vec.pop Global stack = ok (entry, rest) ∧
      rest.val = stack.val.take (stack.val.length - 1) := by
  cases hpop : alloc.vec.Vec.pop Global stack with
  | fail e =>
    unfold alloc.vec.Vec.pop at hpop
    split at hpop <;> simp at hpop
  | div =>
    unfold alloc.vec.Vec.pop at hpop
    split at hpop <;> simp at hpop
  | ok result =>
    obtain ⟨entry, rest⟩ := result
    refine ⟨entry, rest, rfl, ?_⟩
    cases entry with
    | none =>
      obtain ⟨hstack, hrest⟩ := vec_pop_none_values hpop
      simp [hstack, hrest]
    | some entry => simp [vec_pop_some_values hpop]

/-- The extracted backtracking loop always succeeds and removes exactly the
    requested suffix, saturating at the empty stack. It needs no assumption
    that the pop count is bounded by the current stack length. -/
theorem pop_many_spec {T : Type} (stack : alloc.vec.Vec T) (count : Std.Usize) :
    ∃ result, pop_many stack count = ok result ∧
      result.val = stack.val.take (stack.val.length - count.val) := by
  generalize hcount : count.val = n
  induction n generalizing count stack with
  | zero =>
    have hz : count = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hcount
    subst count
    refine ⟨stack, ?_, by simp⟩
    rw [pop_many, pop_many_loop, loop]
    simp [pop_many_loop.body]
  | succ n ih =>
    obtain ⟨previous, hprevious, hpreviousVal⟩ := usize_sub_one_succeeds (x := count) (by omega)
    have hpre : previous.val = n := by omega
    obtain ⟨entry, rest, hpop, hrest⟩ := vec_pop_spec stack
    obtain ⟨result, hloop, hvalues⟩ := ih (count := previous) (stack := rest) hpre
    refine ⟨result, ?_, ?_⟩
    · rw [pop_many, pop_many_loop, loop]
      have hpositive : count > 0#usize := by scalar_tac
      simp! only [pop_many_loop.body, if_pos hpositive, hpop, hprevious, bind_tc_ok]
      exact hloop
    · have hrestLen : rest.val.length = stack.val.length - 1 := by simp [hrest]
      rw [hrestLen, hrest, _root_.List.take_take] at hvalues
      have hmin : min (stack.val.length - 1 - n) (stack.val.length - 1) =
          stack.val.length - 1 - n := by omega
      rw [hmin] at hvalues
      simpa [Nat.sub_sub, Nat.add_comm] using hvalues

end milhouse.iter
