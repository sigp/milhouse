import Tree.Builder.Carry

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- A merge position below the root has a representable bit address, and its
checked packing-depth addition and right shift return the mathematical bits. -/
theorem Builder.finish_merge_shift_success (cursor index packing root : Std.Usize)
    (hindex : index.val < root.val)
    (hroot : root.val + packing.val < System.Platform.numBits) :
    ∃ shift shifted, index + packing = ok shift ∧ cursor >>> shift = ok shifted ∧
      shifted.val = cursor.val >>> (index.val + packing.val) := by
  have hbound : index.val + packing.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hbits := System.Platform.numBits_le
    have hlarge : 64 ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨shift, hadd, hshift⟩ := WP.spec_imp_exists (UScalar.add_spec hbound)
  obtain ⟨shifted, hright, hval, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftRight_spec cursor shift (by
      rw [hshift, UScalarTy.Usize_numBits_eq]
      omega))
  exact ⟨shift, shifted, hadd, hright, by simpa only [hshift] using hval⟩

/-- Every merge needed to finish a partial packed leaf succeeds. The actual
loop follows the canonical carry plan and stops at its first clear bit or the
root; the vector and counter bounds follow from the supplied stack and depth. -/
theorem Builder.finish_packed_leaf_loop_success {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {count depth len : Nat}
    {input finalStack : _root_.List (utils.MaybeArced (tree.Tree T))}
    {top finalTop : tree.Tree T}
    (hplan : BuilderMergePlan ValueInst factor count input top finalStack finalTop depth len)
    (self : Builder T) (cursor index : Std.Usize)
    (hbits : BuilderMergeBits cursor.val index.val count self.depth.val self.packing_depth.val)
    (hroot : self.depth.val + self.packing_depth.val < System.Platform.numBits)
    (hstack : self.stack.val = input ++ [utils.MaybeArced.Unarced top]) :
    ∃ forest, Builder.finish_packed_leaf_loop ValueInst self cursor index =
      ok (core.result.Result.Ok (), forest, self.depth, self.level, self.length,
        self.packing_factor, self.packing_depth, self.capacity) ∧
      forest.val = finalStack ++ [utils.MaybeArced.Unarced finalTop] := by
  induction hplan generalizing self index with
  | done input top depth len hdense hpositive =>
    refine ⟨self.stack, ?_, hstack⟩
    have hbody : Builder.finish_packed_leaf_loop.body ValueInst cursor self index =
        ok (.done (core.result.Result.Ok (), self.stack, self.depth, self.level, self.length,
          self.packing_factor, self.packing_depth, self.capacity)) := by
      by_cases hlt : index < self.depth
      · obtain ⟨shift, shifted, hadd, hright, hval⟩ := Builder.finish_merge_shift_success cursor index
          self.packing_depth self.depth hlt hroot
        have hstop : ((cursor.val >>> (index.val + self.packing_depth.val)) &&& 1) = 0 := by
          rcases hbits.stop with hroot | hstop
          · change index.val < self.depth.val at hlt
            omega
          · simpa only [Nat.add_zero] using hstop
        have hbit : shifted &&& 1#usize = 0#usize := by
          apply UScalar.eq_of_val_eq
          simpa [hval] using hstop
        simp only [Builder.finish_packed_leaf_loop.body, hlt, ↓reduceIte, hadd,
          hright, hbit, lift, bind_tc_ok, show (0#usize) ≠ 1#usize by decide, ↓reduceIte]
      · simp only [Builder.finish_packed_leaf_loop.body, hlt, ↓reduceIte]
    rw [Builder.finish_packed_leaf_loop, loop]
    simp! only [hbody, bind_tc_ok]
  | @step input left top merged depth len count finalStack finalTop finalDepth finalLen
      hleft htop hpositive hmerge hplan ih =>
    have hmergeBit := hbits.merge 0 (by omega)
    have hlt : index < self.depth := by
      change index.val < self.depth.val
      simpa only [Nat.add_zero] using hmergeBit.1
    obtain ⟨shift, shifted, hadd, hright, hval⟩ := Builder.finish_merge_shift_success cursor index
      self.packing_depth self.depth hlt hroot
    have hbit : shifted &&& 1#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      simpa [hval] using hmergeBit.2
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
    have hnextBits : BuilderMergeBits cursor.val next.val count advanced.depth.val
        advanced.packing_depth.val := by
      constructor
      · intro offset hoffset
        have h := hbits.merge (offset + 1) (by omega)
        simpa only [advanced, hnextVal, show (1#usize).val = 1 from rfl,
          Nat.add_assoc, Nat.add_comm 1] using h
      · simpa only [advanced, hnextVal, show (1#usize).val = 1 from rfl,
          Nat.add_assoc, Nat.add_comm 1] using hbits.stop
    obtain ⟨forest, hloop, hforest⟩ := ih advanced next hnextBits hroot
      (by simp only [advanced, hpushed, hrest])
    refine ⟨forest, ?_, hforest⟩
    have hbody : Builder.finish_packed_leaf_loop.body ValueInst cursor self index =
        ok (.cont (advanced, next)) := by
      simp! only [Builder.finish_packed_leaf_loop.body, hlt, ↓reduceIte, hadd, hright,
        hbit, lift, bind_tc_ok, hpopTop, hpopLeft, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, maybeArced_arced, maybeArcedTree_unarced,
        triomphe.arc.Arc.new, hmerge, hpush, hnext, advanced]
    rw [Builder.finish_packed_leaf_loop, loop]
    simp! only [hbody, bind_tc_ok]
    exact hloop

end milhouse.builder
