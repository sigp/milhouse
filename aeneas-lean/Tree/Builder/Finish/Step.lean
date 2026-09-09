import Tree.Builder.Finish.LevelMerge

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

private theorem pow_two_success (exponent : Std.Usize)
    (hbits : exponent.val < System.Platform.numBits) :
    ∃ increment, core.num.Usize.pow 2#usize (UScalar.cast .U32 exponent) = ok increment ∧
      increment.val = 2 ^ exponent.val := by
  have hcast : (UScalar.cast .U32 exponent).val = exponent.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have hplatform := System.Platform.numBits_le
    change exponent.val < 2 ^ 32
    omega
  have hfit : UScalar.inBounds .Usize (2 ^ exponent.val) :=
    Nat.pow_lt_pow_right (by decide) hbits
  have hspec := UScalar.tryMk_eq .Usize (2 ^ exponent.val)
  cases htry : UScalar.tryMk .Usize (2 ^ exponent.val) with
  | ok increment =>
    simp only [htry] at hspec
    exact ⟨increment, by simpa only [core.num.Usize.pow, hcast, show (2#usize).val = 2 from rfl] using htry,
      hspec.1⟩
  | fail error => simp only [htry] at hspec; exact (hspec hfit).elim
  | div => simp only [htry] at hspec

/-- Every nonterminal finish step pads one final subtree, performs its
canonical carries, and strictly advances the physical cursor. The forest
remains normalized and the logical contents and builder metadata retain their
original meaning. All allocation and arithmetic bounds follow internally. -/
theorem Builder.finish_tree_body_success {T : Type} {ValueInst : Value T}
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
    (hpartial : physical < subtreeCapacity self.packing_factor self.depth.val)
    (hcursor : physical = cursor.val * 2 ^ self.level.val) :
    ∃ forest next, Builder.finish_tree_loop.body ValueInst self cursor =
      ok (.cont ({ self with stack := forest }, next)) ∧
      BuilderNormalizedStack self.packing_factor base forest.val self.depth.val logical
        (next.val * 2 ^ self.level.val) ∧ physical < next.val * 2 ^ self.level.val := by
  obtain ⟨prefixStack, top, topDepth, prefixLen, topLen, hstack, hbaseTop, htopDepth,
      htop, htopPositive, hprefix, haligned, hlogical, hphysical⟩ :=
    hnormalized.split_last_of_not_full hlayout hpositive hpartial
  have hlevelTop : self.level.val ≤ topDepth + self.packing_depth.val := by
    rw [hbase] at hbaseTop
    by_cases hzero : self.level.val = 0
    · omega
    · have hpacking := hlevelValid.resolve_left hzero
      simp only [hzero, ↓reduceIte] at hbaseTop
      omega
  have hfit : cursor.val * 2 ^ self.level.val < 2 ^ System.Platform.numBits := by
    rw [← hcursor]
    have hbound : self.capacity.val < 2 ^ System.Platform.numBits := self.capacity.hBounds
    omega
  have hlevel : self.level.val < System.Platform.numBits := by omega
  obtain ⟨shifted, hshift, hshiftVal⟩ := Builder.finish_cursor_shift_success cursor self.level hlevel hfit
  have hcontinue : (shifted != self.capacity) = true := by
    have hne : shifted ≠ self.capacity := by
      intro heq
      have := congrArg UScalar.val heq
      omega
    simpa only [bne_iff_ne] using hne
  obtain ⟨units, hunits⟩ := Nat.dvd_of_mod_eq_zero haligned
  have hunitsEq : prefixLen = subtreeCapacity self.packing_factor (topDepth + 1) * units := by
    simpa only [Nat.mul_comm] using hunits
  obtain ⟨zeros, hzeros⟩ : ∃ zeros, core.num.Usize.trailing_zeros cursor = ok zeros := ⟨_, rfl⟩
  let depth := core.num.Usize.saturating_sub
    (core.num.Usize.saturating_add (UScalar.cast .Usize zeros) self.level) self.packing_depth
  have hdepth : depth.val = topDepth :=
    finish_top_depth_eq hlayout hunitsEq htopDepth hphysical hcursor hlevelTop hroot hzeros
  obtain ⟨rest, hpop, hrest⟩ := vec_pop_append_last (A := Global) self.stack prefixStack top hstack
  obtain ⟨zero, hzero, hzeroDense⟩ := zero_preserves_dense ValueInst self.packing_factor depth
  obtain ⟨padded, hpad, _⟩ := node_unboxed_preserves_dense ValueInst (maybeArcedTree top) zero
    topDepth topLen 0 htop (by simpa only [hdepth] using hzeroDense) htopPositive (by simp)
  have hroom : rest.val.length < Std.Usize.max := by
    have hlen := self.stack.property
    rw [hstack] at hlen
    simp only [_root_.List.length_append, _root_.List.length_singleton] at hlen
    rw [hrest]
    omega
  obtain ⟨paddedStack, hpush, hpushed⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec rest (utils.MaybeArced.Unarced padded) hroom)
  obtain ⟨count, finalStack, finalTop, finalDepth, finalLen, hplan, hcarry, hnormalizedNext⟩ :=
    hprefix.finish_padding_plan hlayout (Nat.le_succ_of_le hbaseTop) haligned htop htopPositive
      (by simpa only [hdepth] using hzeroDense) hpad hlogical hphysical hnormalized.physical_le_capacity
  have hmergeBits := hcarry.finish_merge_bits hlayout hphysical
  have hstartBound : depth.val + (1#usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hdepthMax : self.depth.val ≤ Std.Usize.max := by scalar_tac
    change depth.val + 1 ≤ Std.Usize.max
    omega
  obtain ⟨start, hstart, hstartVal⟩ := WP.spec_imp_exists (UScalar.add_spec hstartBound)
  let prepared := { self with stack := paddedStack }
  obtain ⟨forest, hloop, hforest⟩ := Builder.finish_level_loop_success hplan prepared cursor start
    (by simpa only [prepared, hstartVal, show (1#usize).val = 1 from rfl,
      hdepth, ← hcursor] using hmergeBits)
    hroot hlevel hfit (by simp only [prepared, hpushed, hrest])
  have hfinish : Builder.finish_level ValueInst prepared cursor depth =
      ok (core.result.Result.Ok (), { self with stack := forest }) := by
    simp! only [Builder.finish_level, hstart, hloop, bind_tc_ok, prepared]
  have hdepthBound : depth.val + self.packing_depth.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hplatform := System.Platform.numBits_le
    have hlarge : 64 ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨packedDepth, hdepthAdd, hpackedDepth⟩ := WP.spec_imp_exists (UScalar.add_spec hdepthBound)
  obtain ⟨exponent, hsub, hexponent, _⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := packedDepth) (y := self.level) (by omega))
  have hexponentBits : exponent.val < System.Platform.numBits := by omega
  obtain ⟨increment, hpow, hincrement⟩ := pow_two_success exponent hexponentBits
  have hnextPhysical : (cursor.val + increment.val) * 2 ^ self.level.val =
      physical + subtreeCapacity self.packing_factor topDepth := by
    rw [Nat.add_mul, ← hcursor, hincrement, ← pow_add, hlayout.subtreeCapacity_eq_two_pow]
    congr 2
    omega
  have hnextBound : cursor.val + increment.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hle := Nat.le_mul_of_pos_right (cursor.val + increment.val) (Nat.two_pow_pos self.level.val)
    rw [hnextPhysical] at hle
    have hfits := hnormalizedNext.physical_le_capacity
    have hcapMax : self.capacity.val ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨next, hnext, hnextVal⟩ := WP.spec_imp_exists (UScalar.add_spec hnextBound)
  have hphysicalNext : next.val * 2 ^ self.level.val =
      physical + subtreeCapacity self.packing_factor topDepth := by
    simpa only [hnextVal] using hnextPhysical
  refine ⟨forest, next, ?_, ?_, ?_⟩
  · dsimp only [depth, prepared] at hzero hfinish hdepthAdd
    simp! only [Builder.finish_tree_loop.body, hshift, bind_tc_ok, hcontinue, ↓reduceIte,
      hzeros, lift, hpop, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      maybeArced_arced, hzero, hpad, hpush, hfinish, hdepthAdd, hsub, hpow, hnext]
  · rw [hforest, hphysicalNext]
    exact hnormalizedNext
  · rw [hphysicalNext]
    have hpositive := hlayout.subtreeCapacity_pos topDepth
    omega

end milhouse.builder
