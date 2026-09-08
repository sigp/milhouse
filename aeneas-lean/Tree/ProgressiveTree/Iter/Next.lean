import Tree.ProgressiveTree.Iter.Step

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

private theorem next_loop_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (values : _root_.List T)
    (hvalid : ProgressiveTreeIter.Valid ValueInst factor self values) :
    ∃ next,
      ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next_loop ValueInst self =
        ok (next, values.head?) ∧
      ProgressiveTreeIter.Valid ValueInst factor next values.tail ∧
      next.length = self.length ∧
      next.yielded.val = self.yielded.val + min 1 values.length := by
  generalize hm : ProgressiveTreeIter.pendingSteps self.current_prog_node = remaining
  induction remaining using Nat.strong_induction_on generalizing self with
  | h remaining ih =>
    obtain ⟨flow, next, hstep, hlength, hpost⟩ :=
      ProgressiveTreeIter.next_step_spec ValueInst hlayout self values hvalid
    cases flow with
    | Continue unit =>
      obtain ⟨hnextValid, hyielded, hdecrease⟩ := hpost
      obtain ⟨rest, hloop, hrestValid, hrestLength, hrestYielded⟩ :=
        ih (ProgressiveTreeIter.pendingSteps next.current_prog_node) (by omega) next hnextValid rfl
      refine ⟨rest, ?_, hrestValid, hrestLength.trans hlength, ?_⟩
      · rw [ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next_loop, loop]
        simp! only [ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next_loop.body,
          hstep, bind_tc_ok]
        exact hloop
      · simpa [hyielded] using hrestYielded
    | Break value =>
      obtain ⟨rfl, hnextValid, hyielded⟩ := hpost
      refine ⟨next, ?_, hnextValid, hlength, hyielded⟩
      rw [ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next_loop, loop]
      simp! only [ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next_loop.body,
        hstep, bind_tc_ok]

/-- Complete progressive `next` terminates, skips any empty layers, and returns
    exactly the head of the represented suffix. Its result retains the cursor
    invariant for the tail, including after exhaustion, so repeated exhausted
    calls remain successful and return `none`. -/
theorem ProgressiveTreeIter.next_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (values : _root_.List T)
    (hvalid : ProgressiveTreeIter.Valid ValueInst factor self values) :
    ∃ next,
      ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        ok (values.head?, next) ∧
      ProgressiveTreeIter.Valid ValueInst factor next values.tail ∧
      next.length = self.length ∧
      next.yielded.val = self.yielded.val + min 1 values.length := by
  obtain ⟨next, hloop, hvalid, hlength, hyielded⟩ := next_loop_spec ValueInst hlayout self values hvalid
  refine ⟨next, ?_, hvalid, hlength, hyielded⟩
  simp! only [ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    hloop, bind_tc_ok]

/-- A valid progressive cursor enumerates its complete remaining sequence
    through the first `none`; termination follows from the proved next-call
    invariant, without an iterator-output or successful-call premise. -/
theorem ProgressiveTreeIter.yields {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (values : _root_.List T)
    (hvalid : ProgressiveTreeIter.Valid ValueInst factor self values) :
    IteratorYields (ProgressiveTreeIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
      self values := by
  induction values generalizing self with
  | nil =>
    obtain ⟨next, hnext, _⟩ := ProgressiveTreeIter.next_spec ValueInst hlayout self [] hvalid
    exact .nil hnext
  | cons value values ih =>
    obtain ⟨next, hnext, hvalid, _⟩ := ProgressiveTreeIter.next_spec ValueInst hlayout self (value :: values) hvalid
    exact .cons hnext (ih next hvalid)

end milhouse.progressive_tree
