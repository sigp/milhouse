import Tree.Builder.Finish.Finalize
import Tree.Builder.Finish.Packed
import Tree.Builder.Contents

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

private theorem div_ceil_success (value divisor : Std.Usize) (hpositive : 0 < divisor.val) :
    ∃ quotient, core.num.Usize.div_ceil value divisor = ok quotient ∧
      quotient.val = value.val / divisor.val + if value.val % divisor.val = 0 then 0 else 1 := by
  have hbound : value.val / divisor.val + (if value.val % divisor.val = 0 then 0 else 1) ≤ value.val := by
    split_ifs with hrem
    · simpa only [Nat.add_zero] using Nat.div_le_self value.val divisor.val
    · have hvalue : 0 < value.val := by
        by_contra h
        have hz : value.val = 0 := by omega
        simp only [hz, Nat.zero_mod, not_true_eq_false] at hrem
      have hdivisor : 1 < divisor.val := by
        by_contra h
        have hone : divisor.val = 1 := by omega
        simp only [hone, Nat.mod_one, not_true_eq_false] at hrem
      exact Nat.succ_le_of_lt (Nat.div_lt_self hvalue hdivisor)
  have hfit : UScalar.inBounds .Usize
      (value.val / divisor.val + if value.val % divisor.val = 0 then 0 else 1) :=
    lt_of_le_of_lt hbound value.hBounds
  have hspec := UScalar.tryMk_eq .Usize
    (value.val / divisor.val + if value.val % divisor.val = 0 then 0 else 1)
  cases htry : UScalar.tryMk .Usize
      (value.val / divisor.val + if value.val % divisor.val = 0 then 0 else 1) with
  | ok quotient =>
    simp only [htry] at hspec
    exact ⟨quotient, by simpa only [core.num.Usize.div_ceil, Nat.ne_of_gt hpositive, ↓reduceIte] using htry,
      hspec.1⟩
  | fail error => simp only [htry] at hspec; exact (hspec hfit).elim
  | div => simp only [htry] at hspec

private theorem packing_skip_success (length factor : Std.Usize) (hpositive : 0 < factor.val) :
    ∃ remainder skip, length % factor = ok remainder ∧
      core.num.Usize.saturating_sub factor remainder % factor = ok skip ∧
      skip.val = (factor.val - length.val % factor.val) % factor.val := by
  obtain ⟨remainder, hrem, hremVal⟩ := WP.spec_imp_exists
    (UScalar.rem_spec length (y := factor) (Nat.ne_of_gt hpositive))
  obtain ⟨skip, hskip, hskipVal⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (core.num.Usize.saturating_sub factor remainder)
      (y := factor) (Nat.ne_of_gt hpositive))
  have hsub : (core.num.Usize.saturating_sub factor remainder).val = factor.val - remainder.val := by
    unfold core.num.Usize.saturating_sub UScalar.saturating_sub UScalar.val
    rw [max_eq_right (Nat.zero_le _), BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.sub_le factor.val remainder.val).trans_lt factor.hBounds)
  exact ⟨remainder, skip, hrem, hskip, by simpa only [hsub, hremVal] using hskipVal⟩

/-- Every valid binary builder finishes successfully, including empty,
partially packed, and nonzero-level builders. All arithmetic and finalization
conditions follow from the complete builder invariant. -/
theorem Builder.finish_success {T : Type} {ValueInst : Value T}
    (self : Builder T) (hinvariant : BuilderInvariant ValueInst self) :
    ∃ tree, Builder.finish ValueInst self =
      ok (core.result.Result.Ok (tree, self.depth, self.length)) := by
  have hlayout := BuilderInvariant.layout hinvariant
  have hcapacity := BuilderInvariant.builder_capacity_matches hinvariant
  have hroot := BuilderInvariant.depth_packing_lt_bits hinvariant
  have hcapMax : self.capacity.val ≤ Std.Usize.max := by scalar_tac
  by_cases hempty : self.stack.val = []
  · have hzero : self.length = 0#usize := UScalar.eq_of_val_eq
      ((BuilderInvariant.stack_dense hinvariant).length_eq_zero_of_nil hempty)
    obtain ⟨tree, htree, _⟩ := zero_preserves_dense ValueInst self.packing_factor self.depth
    refine ⟨tree, ?_⟩
    simp only [Builder.finish, alloc.vec.Vec.is_empty, hempty, _root_.List.isEmpty_nil,
      bind_tc_ok, ↓reduceIte, htree, hzero]
  · have hpositive : 0 < self.length.val := by
      by_contra h
      exact hempty ((BuilderInvariant.stack_dense hinvariant).eq_nil_of_length_zero (by omega))
    have hnotEmpty : alloc.vec.Vec.is_empty Global self.stack = ok false := by
      simp [alloc.vec.Vec.is_empty, hempty]
    have hlevel : self.level.val < System.Platform.numBits := by
      have hbound := BuilderInvariant.level_bounded hinvariant
      omega
    obtain ⟨levelCapacity, hlevelCapacity, hlevelCapacityVal⟩ :=
      Builder.finish_cursor_shift_success 1#usize self.level hlevel
        (by simpa only [show (1#usize).val = 1 from rfl, Nat.one_mul] using
          Nat.pow_lt_pow_right (by decide : 1 < 2) hlevel)
    simp only [show (1#usize).val = 1 from rfl, Nat.one_mul] at hlevelCapacityVal
    obtain ⟨cursor, hcursor, hcursorVal⟩ := div_ceil_success self.length levelCapacity
      (by rw [hlevelCapacityVal]; positivity)
    have hready : (self.level.val ≠ 0 ∨
        self.length.val % subtreeCapacity self.packing_factor
          (if self.level.val = 0 then 0 else self.level.val - self.packing_depth.val) = 0) →
        ∃ tree, finishTreeAndFinalize ValueInst self cursor =
          ok (core.result.Result.Ok (tree, self.depth, self.length)) := by
      intro hready
      obtain ⟨physical, hnormalized, hphysical⟩ := hinvariant.finish_cursor_normalized
        hlevelCapacity hcursor hready
      obtain ⟨tree, hfinish, _⟩ := finishTreeAndFinalize_success self cursor hlayout
        (BuilderInvariant.level_valid hinvariant) hcapacity hroot hnormalized rfl hpositive hphysical
      exact ⟨tree, hfinish⟩
    cases hfactor : self.packing_factor with
    | none =>
      obtain ⟨tree, hfinish⟩ := hready (by
        by_cases hzero : self.level.val = 0
        · exact Or.inr (by
            simp only [hzero, ↓reduceIte, hfactor, subtreeCapacity, leafCapacity, pow_zero, Nat.one_mul]
            exact Nat.mod_one _)
        · exact Or.inl hzero)
      refine ⟨tree, ?_⟩
      simp only [Builder.finish, hnotEmpty, Bool.false_eq_true, ↓reduceIte,
        utils.Length.as_usize, bind_tc_ok, hlevelCapacity, hcursor, hfactor]
      exact hfinish
    | some factor =>
      have hfactorPositive : 0 < factor.val := by
        simpa only [hfactor, leafCapacity] using hlayout.leafCapacity_pos
      obtain ⟨remainder, skip, hrem, hskip, hskipVal⟩ := packing_skip_success self.length factor hfactorPositive
      by_cases hlevelZero : self.level.val = 0
      · have hlevelEq : self.level = 0#usize := UScalar.eq_of_val_eq hlevelZero
        have hcursorEq : cursor = self.length := by
          apply UScalar.eq_of_val_eq
          simpa only [hlevelCapacityVal, hlevelZero, pow_zero, Nat.div_one, Nat.mod_one,
            ↓reduceIte, Nat.add_zero] using hcursorVal
        by_cases haligned : self.length.val % factor.val = 0
        · have hskipEq : skip = 0#usize := by
            apply UScalar.eq_of_val_eq
            simpa only [haligned, Nat.sub_zero, Nat.mod_self, show (0#usize).val = 0 from rfl] using hskipVal
          obtain ⟨tree, hfinish⟩ := hready (Or.inr (by
            simpa only [hlevelZero, ↓reduceIte, hfactor, subtreeCapacity, leafCapacity,
              pow_zero, Nat.mul_one] using haligned))
          refine ⟨tree, ?_⟩
          simp only [Builder.finish, hnotEmpty, Bool.false_eq_true, ↓reduceIte,
            utils.Length.as_usize, bind_tc_ok, hlevelCapacity, hcursor, hfactor,
            hrem, lift, hskip, hskipEq, lt_self_iff_false, ↓reduceIte]
          exact hfinish
        · have hpartial : self.length.val % subtreeCapacity self.packing_factor 0 ≠ 0 := by
            simpa only [hfactor, subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] using haligned
          have hskipMath : skip.val = factor.val - self.length.val % factor.val := by
            rw [hskipVal, Nat.mod_eq_of_lt]
            have hremLess := Nat.mod_lt self.length.val hfactorPositive
            omega
          have hskipPositive : skip > 0#usize := by
            change 0 < skip.val
            have hremLess := Nat.mod_lt self.length.val hfactorPositive
            omega
          obtain ⟨forest, hpacked, hnormalized⟩ := Builder.finish_packed_leaf_success self hinvariant hlevelZero hpartial
          have hphysical : self.length.val + subtreeCapacity self.packing_factor 0 -
              self.length.val % subtreeCapacity self.packing_factor 0 = self.length.val + skip.val := by
            simp only [hfactor, subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one]
            have hremLess := Nat.mod_lt self.length.val hfactorPositive
            omega
          have hbound : self.length.val + skip.val ≤ UScalar.max .Usize := by
            rw [UScalar.max_USize_eq]
            have hfits := hnormalized.physical_le_capacity
            rw [hphysical] at hfits
            omega
          obtain ⟨next, hnext, hnextVal⟩ := WP.spec_imp_exists (UScalar.add_spec hbound)
          let prepared := { self with stack := forest }
          obtain ⟨tree, hfinish, _⟩ := finishTreeAndFinalize_success prepared next hlayout
            (Or.inl hlevelZero) hcapacity hroot hnormalized
            (by simp only [prepared, hlevelZero, ↓reduceIte]) hpositive
            (by simp only [prepared, hlevelZero, pow_zero, Nat.mul_one, hnextVal, hphysical])
          refine ⟨tree, ?_⟩
          rw [hlevelEq] at hlevelCapacity
          simp! only [Builder.finish, hnotEmpty, Bool.false_eq_true, ↓reduceIte,
            utils.Length.as_usize, bind_tc_ok, hlevelCapacity, hcursor, hcursorEq, hfactor,
            hrem, lift, hskip, hskipPositive, hlevelEq, hpacked,
            core.result.Result.Insts.CoreOpsTry.branch, hnext]
          simp only [finishTreeAndFinalize, prepared, hlevelEq, hfactor, bind_eq_ok_iff] at hfinish
          obtain ⟨⟨status, finished⟩, htree, hfinish⟩ := hfinish
          simp! only [htree, bind_tc_ok]
          exact hfinish
      · have hlevelNe : self.level ≠ 0#usize := by
          intro heq
          exact hlevelZero (congrArg UScalar.val heq)
        obtain ⟨tree, hfinish⟩ := hready (Or.inl hlevelZero)
        refine ⟨tree, ?_⟩
        simp only [Builder.finish, hnotEmpty, Bool.false_eq_true, ↓reduceIte,
          utils.Length.as_usize, bind_tc_ok, hlevelCapacity, hcursor, hfactor,
          hrem, lift, hskip]
        split <;> exact hfinish

/-- Total sequence-level finalization: every valid builder returns all its
values in order, with its exact depth, logical length, and a dense root. -/
theorem Builder.finish_total_spec {T : Type} {ValueInst : Value T}
    (self : Builder T) (hinvariant : BuilderInvariant ValueInst self) :
    ∃ tree, Builder.finish ValueInst self =
      ok (core.result.Result.Ok (tree, self.depth, self.length)) ∧
      tree.elements = self.elements ∧ self.length.val = self.elements.length ∧
      DenseTree self.packing_factor tree self.depth.val self.elements.length := by
  obtain ⟨tree, hfinish⟩ := Builder.finish_success self hinvariant
  obtain ⟨helements, _, hlength, hdense⟩ := Builder.finish_spec hinvariant hfinish
  exact ⟨tree, hfinish, helements, hlength, hdense⟩

end milhouse.builder
