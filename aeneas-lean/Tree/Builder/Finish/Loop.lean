import Tree.Builder.Finish.Step

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- A nonempty normalized builder always finishes its padding loop. Each
iteration reduces the gap to capacity, and the result is a physically full
normalized forest with the original logical length and configuration. -/
theorem Builder.finish_tree_loop_success {T : Type} {ValueInst : Value T}
    (self : Builder T) (cursor : Std.Usize)
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hlevelValid : self.level.val = 0 ∨ self.packing_depth.val ≤ self.level.val)
    (hcapacity : self.capacity.val = subtreeCapacity self.packing_factor self.depth.val)
    (hroot : self.depth.val + self.packing_depth.val < System.Platform.numBits)
    {base logical physical : Nat}
    (hnormalized : BuilderNormalizedStack self.packing_factor base self.stack.val
      self.depth.val logical physical)
    (hbase : base = if self.level.val = 0 then 0 else self.level.val - self.packing_depth.val)
    (hpositive : 0 < logical)
    (hcursor : physical = cursor.val * 2 ^ self.level.val) :
    ∃ forest, Builder.finish_tree_loop ValueInst self cursor =
      ok (core.result.Result.Ok (), { self with stack := forest }) ∧
      BuilderNormalizedStack self.packing_factor base forest.val self.depth.val logical self.capacity.val := by
  by_cases hfull : physical = self.capacity.val
  · have hlevel : self.level.val < System.Platform.numBits := by
      have hbaseDepth := hnormalized.base_le_depth
      rw [hbase] at hbaseDepth
      by_cases hzero : self.level.val = 0
      · omega
      · have hpacking := hlevelValid.resolve_left hzero
        simp only [hzero, ↓reduceIte] at hbaseDepth
        omega
    obtain ⟨shifted, hshift, hval⟩ := Builder.finish_cursor_shift_success cursor self.level hlevel
      (by rw [← hcursor, hfull]; exact self.capacity.hBounds)
    have heq : shifted = self.capacity := by
      apply UScalar.eq_of_val_eq
      omega
    have hbody : Builder.finish_tree_loop.body ValueInst self cursor =
        ok (.done (core.result.Result.Ok (), self)) := by
      simp only [Builder.finish_tree_loop.body, hshift, heq, bind_tc_ok, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
    refine ⟨self.stack, ?_, by simpa only [hfull] using hnormalized⟩
    rw [Builder.finish_tree_loop, loop]
    simp! only [hbody, bind_tc_ok]
  · have hpartial : physical < subtreeCapacity self.packing_factor self.depth.val := by
      have hle := hnormalized.physical_le_capacity
      omega
    obtain ⟨forest, next, hbody, hnormalizedNext, hprogress⟩ := Builder.finish_tree_body_success
      self cursor hlayout hlevelValid hcapacity hroot hnormalized hbase hpositive hpartial hcursor
    let advanced := { self with stack := forest }
    obtain ⟨finished, hloop, hnormalizedFinished⟩ := Builder.finish_tree_loop_success
      advanced next hlayout hlevelValid hcapacity hroot hnormalizedNext hbase hpositive rfl
    refine ⟨finished, ?_, hnormalizedFinished⟩
    rw [Builder.finish_tree_loop, loop]
    simp! only [hbody, bind_tc_ok]
    exact hloop
termination_by self.capacity.val - physical
decreasing_by
  omega

end milhouse.builder
