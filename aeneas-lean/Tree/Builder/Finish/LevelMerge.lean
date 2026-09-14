import Tree.Builder.Finish.PackedMerge

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- A fitting level-scaled cursor is exactly its logical offset after the
actual checked shift. -/
theorem Builder.finish_cursor_shift_success (cursor level : Std.Usize)
    (hlevel : level.val < System.Platform.numBits)
    (hfit : cursor.val * 2 ^ level.val < 2 ^ System.Platform.numBits) :
    ∃ shifted, cursor <<< level = ok shifted ∧ shifted.val = cursor.val * 2 ^ level.val := by
  obtain ⟨shifted, hshift, hval, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec cursor level (UScalar.size .Usize) hlevel rfl)
  refine ⟨shifted, hshift, ?_⟩
  simpa only [Nat.shiftLeft_eq, UScalar.size, UScalarTy.Usize_numBits_eq,
    Nat.mod_eq_of_lt hfit] using hval

/-- The finish-level loop performs every prescribed carry and succeeds at
the first clear bit or the root. Logical offsets are obtained from the actual
level-scaled cursor, and all vector and increment bounds follow internally. -/
theorem Builder.finish_level_loop_success {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {count depth len : Nat}
    {input finalStack : _root_.List (utils.MaybeArced (tree.Tree T))}
    {top finalTop : tree.Tree T}
    (hplan : BuilderMergePlan ValueInst factor count input top finalStack finalTop depth len)
    (self : Builder T) (cursor index : Std.Usize)
    (hbits : BuilderMergeBits (cursor.val * 2 ^ self.level.val) index.val count
      self.depth.val self.packing_depth.val)
    (hroot : self.depth.val + self.packing_depth.val < System.Platform.numBits)
    (hlevel : self.level.val < System.Platform.numBits)
    (hfit : cursor.val * 2 ^ self.level.val < 2 ^ System.Platform.numBits)
    (hstack : self.stack.val = input ++ [utils.MaybeArced.Unarced top]) :
    ∃ forest, Builder.finish_level_loop ValueInst self cursor index =
      ok (core.result.Result.Ok (), forest, self.depth, self.level, self.length,
        self.packing_factor, self.packing_depth, self.capacity) ∧
      forest.val = finalStack ++ [utils.MaybeArced.Unarced finalTop] := by
  induction hplan generalizing self index with
  | done input top depth len hdense hpositive =>
    refine ⟨self.stack, ?_, hstack⟩
    have hbody : Builder.finish_level_loop.body ValueInst cursor self index =
        ok (.done (core.result.Result.Ok (), self.stack, self.depth, self.level, self.length,
          self.packing_factor, self.packing_depth, self.capacity)) := by
      by_cases hlt : index < self.depth
      · obtain ⟨logical, hleft, hlogical⟩ := Builder.finish_cursor_shift_success cursor self.level hlevel hfit
        obtain ⟨shift, shifted, hadd, hright, hval⟩ := Builder.finish_merge_shift_success logical index
          self.packing_depth self.depth hlt hroot
        have hstop : (((cursor.val * 2 ^ self.level.val) >>>
            (index.val + self.packing_depth.val)) &&& 1) = 0 := by
          rcases hbits.stop with hroot | hstop
          · change index.val < self.depth.val at hlt
            omega
          · simpa only [Nat.add_zero] using hstop
        have hbit : shifted &&& 1#usize = 0#usize := by
          apply UScalar.eq_of_val_eq
          simpa [hval, hlogical] using hstop
        simp only [Builder.finish_level_loop.body, hlt, ↓reduceIte, hleft, hadd,
          hright, hbit, lift, bind_tc_ok, show (0#usize) ≠ 1#usize by decide, ↓reduceIte]
      · simp only [Builder.finish_level_loop.body, hlt, ↓reduceIte]
    rw [Builder.finish_level_loop, loop]
    simp! only [hbody, bind_tc_ok]
  | @step input left top merged depth len count finalStack finalTop finalDepth finalLen
      hleftDense htop hpositive hmerge hplan ih =>
    have hmergeBit := hbits.merge 0 (by omega)
    have hlt : index < self.depth := by
      change index.val < self.depth.val
      simpa only [Nat.add_zero] using hmergeBit.1
    obtain ⟨logical, hleft, hlogical⟩ := Builder.finish_cursor_shift_success cursor self.level hlevel hfit
    obtain ⟨shift, shifted, hadd, hright, hval⟩ := Builder.finish_merge_shift_success logical index
      self.packing_depth self.depth hlt hroot
    have hbit : shifted &&& 1#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      simpa [hval, hlogical] using hmergeBit.2
    obtain ⟨afterTop, hpopTop, hafterTop⟩ := vec_pop_append_last (A := Global) self.stack
      (input ++ [left]) (utils.MaybeArced.Unarced top) hstack
    obtain ⟨rest, hpopLeft, hrest⟩ := vec_pop_append_last (A := Global) afterTop input left hafterTop
    have hroom : rest.val.length < Std.Usize.max := by
      have hlen := self.stack.property
      rw [hstack] at hlen
      simp only [_root_.List.length_append, _root_.List.length_singleton] at hlen
      rw [hrest]
      omega
    obtain ⟨pushed, hpush, hpushed⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec rest (utils.MaybeArced.Unarced merged) hroom)
    have hnextBound : index.val + (1#usize).val ≤ UScalar.max .Usize := by
      rw [UScalar.max_USize_eq]
      have hdepthMax : self.depth.val ≤ Std.Usize.max := by scalar_tac
      change index.val < self.depth.val at hlt
      change index.val + 1 ≤ Std.Usize.max
      omega
    obtain ⟨next, hnext, hnextVal⟩ := WP.spec_imp_exists (UScalar.add_spec hnextBound)
    let advanced := { self with stack := pushed }
    have hnextBits : BuilderMergeBits (cursor.val * 2 ^ advanced.level.val) next.val count
        advanced.depth.val advanced.packing_depth.val := by
      constructor
      · intro offset hoffset
        have h := hbits.merge (offset + 1) (by omega)
        simpa only [advanced, hnextVal, show (1#usize).val = 1 from rfl,
          Nat.add_assoc, Nat.add_comm 1] using h
      · simpa only [advanced, hnextVal, show (1#usize).val = 1 from rfl,
          Nat.add_assoc, Nat.add_comm 1] using hbits.stop
    obtain ⟨forest, hloop, hforest⟩ := ih advanced next hnextBits hroot hlevel hfit
      (by simp only [advanced, hpushed, hrest])
    refine ⟨forest, ?_, hforest⟩
    have hbody : Builder.finish_level_loop.body ValueInst cursor self index =
        ok (.cont (advanced, next)) := by
      simp! only [Builder.finish_level_loop.body, hlt, ↓reduceIte, hleft, hadd, hright,
        hbit, lift, bind_tc_ok, hpopTop, hpopLeft, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, maybeArced_arced, maybeArcedTree_unarced,
        triomphe.arc.Arc.new, hmerge, hpush, hnext, advanced]
    rw [Builder.finish_level_loop, loop]
    simp! only [hbody, bind_tc_ok]
    exact hloop

end milhouse.builder
