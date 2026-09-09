import Tree.FunsExternal
import CoreSource.Funs

open Aeneas Aeneas.Std Result

/-- The actual standard-library body calls Default before replacing the
place, with the same returned old value and replacement as the local model.
Default failure/divergence is preserved without a termination assumption. -/
theorem core_take_agrees {T : Type} (inst : core.default.Default T) (value : T) :
    CoreSource.core.mem.take inst value = core.mem.take inst value := rfl

private theorem tryMk_value (value : Std.Usize) :
    UScalar.tryMk .Usize value.val = ok value := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, value.hBounds,
    decide_true, ↓reduceDIte, Result.ofOption]
  congr 1

/-- The pinned standard-library quotient/remainder implementation agrees
with the natural ceiling-division model for every machine-word input.
Zero-divisor failure and the rounding addition are included; no positivity
or arithmetic bound is assumed by the comparison. -/
theorem core_div_ceil_agrees (value divisor : Std.Usize) :
    CoreSource.core.num.Usize.div_ceil value divisor = core.num.Usize.div_ceil value divisor := by
  by_cases hzero : divisor.val = 0
  · have hz : divisor = 0#usize := by scalar_tac
    subst divisor
    simp [CoreSource.core.num.Usize.div_ceil, core.num.Usize.div_ceil, UScalar.div,
      HDiv.hDiv]
  · obtain ⟨quotient, hdiv, hquotient⟩ := UScalar.div_spec value hzero
    obtain ⟨remainder, hrem, hremainder⟩ := WP.spec_imp_exists (UScalar.rem_spec value hzero)
    simp only [CoreSource.core.num.Usize.div_ceil, hdiv, hrem, bind_tc_ok,
      core.num.Usize.div_ceil, hzero, ↓reduceIte]
    change (if 0 < remainder.val then quotient + 1#usize else ok quotient) =
      UScalar.tryMk .Usize
        (value.val / divisor.val + if value.val % divisor.val = 0 then 0 else 1)
    by_cases hmod : value.val % divisor.val = 0
    · have hnot : ¬0 < remainder.val := by omega
      rw [if_neg hnot, if_pos hmod, Nat.add_zero, ← hquotient]
      exact (tryMk_value quotient).symm
    · have hpositive : 0 < value.val := by
        by_contra h
        have hv : value.val = 0 := by omega
        simp only [hv, Nat.zero_mod, not_true_eq_false] at hmod
      have hdivisor : 1 < divisor.val := by
        by_contra h
        have hd : divisor.val = 1 := by omega
        simp only [hd, Nat.mod_one, not_true_eq_false] at hmod
      have hround : value.val / divisor.val + 1 ≤ value.val :=
        Nat.succ_le_of_lt (Nat.div_lt_self hpositive hdivisor)
      obtain ⟨rounded, hadd, hrounded⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := quotient) (y := 1#usize) (by scalar_tac))
      have hroundedValue : rounded.val = value.val / divisor.val + 1 := by scalar_tac
      have hpositiveRem : 0 < remainder.val := by omega
      rw [if_pos hpositiveRem, if_neg hmod, hadd, ← hroundedValue]
      exact (tryMk_value rounded).symm

/-- The standard library selects either the checked product or the maximum.
This equals the local clamping model for every pair of u128 values, including
overflow. Checked multiplication remains an Aeneas foundation primitive. -/
theorem core_saturating_mul_agrees (value other : Std.U128) :
    CoreSource.core.num.U128.saturating_mul value other =
      core.num.U128.saturating_mul value other := by
  have h := U128.checked_mul_bv_spec value other
  cases hm : U128.checked_mul value other with
  | none =>
    simp only [hm] at h
    simp only [CoreSource.core.num.U128.saturating_mul, hm, lift, bind_tc_ok,
      core.num.U128.saturating_mul, Nat.min_eq_left (Nat.le_of_lt h)]
    congr 1
    apply UScalar.eq_of_val_eq
    change core.num.U128.MAX.val = (BitVec.ofNat 128 U128.max).toNat
    simp [core.num.U128.MAX, U128.max, U128.numBits, U128.rMax]
  | some product =>
    simp only [hm] at h
    simp only [CoreSource.core.num.U128.saturating_mul, hm, lift, bind_tc_ok,
      core.num.U128.saturating_mul]
    rw [Nat.min_eq_right h.1, ← h.2.1]
    congr 1
    apply U128.bv_eq_imp_eq
    exact (UScalar.BitVec_ofNat_val product).symm

#print axioms core_take_agrees
#print axioms core_div_ceil_agrees
#print axioms core_saturating_mul_agrees
