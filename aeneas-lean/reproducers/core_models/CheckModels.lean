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

private def boundedU128 (n : Nat) : Option Std.U128 :=
  if n < U128.size then some ⟨BitVec.ofNat _ n⟩ else none

private theorem boundedU128_value (value : Std.U128) :
    boundedU128 value.val = some value := by
  have hbound : value.val < U128.size := by scalar_tac
  simp only [boundedU128, if_pos hbound]
  congr 1
  apply U128.bv_eq_imp_eq
  exact UScalar.BitVec_ofNat_val value

private theorem boundedU128_overflow {n : Nat} (h : U128.max < n) :
    boundedU128 n = none := by
  have hn : ¬n < U128.size := by scalar_tac
  exact if_neg hn

private theorem checked_mul_none {left right : Std.U128}
    (h : U128.checked_mul left right = none) : U128.max < left.val * right.val := by
  simpa only [h] using U128.checked_mul_bv_spec left right

private theorem checked_mul_some {left right product : Std.U128}
    (h : U128.checked_mul left right = some product) :
    product.val = left.val * right.val := by
  have hs := U128.checked_mul_bv_spec left right
  simp only [h] at hs
  exact hs.2.1

private theorem odd_bit (exp : Std.U32) :
    (exp &&& 1#u32) = 1#u32 ↔ exp.val % 2 = 1 := by
  rw [UScalar.eq_equiv]
  have hone : (1#u32).val = 1 := by scalar_tac
  simp only [UScalar.val_and, hone, Nat.and_one_is_mod]

private theorem pow_even (base exp : Nat) (h : exp % 2 = 0) :
    base ^ exp = (base * base) ^ (exp / 2) := by
  have he : exp = 2 * (exp / 2) := by omega
  conv_lhs => rw [he]
  rw [Nat.pow_mul, Nat.pow_two]

private theorem pow_odd (base exp : Nat) (h : exp % 2 = 1) :
    base ^ exp = base * (base * base) ^ (exp / 2) := by
  have he : exp = 2 * (exp / 2) + 1 := by omega
  conv_lhs => rw [he]
  rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two, Nat.mul_comm]

private theorem square_le_power (base exp : Nat) (h : 2 ≤ exp) :
    base * base ≤ base ^ exp := by
  by_cases hz : base = 0
  · simp [hz]
  · simpa only [Nat.pow_two] using Nat.pow_le_pow_right (by omega : 0 < base) h

private theorem square_overflow {base acc : Std.U128} {exp : Nat}
    (he : 2 ≤ exp) (ha : 0 < acc.val ∨ base.val = 0)
    (hm : U128.checked_mul base base = none) :
    boundedU128 (acc.val * base.val ^ exp) = none := by
  have hov := checked_mul_none hm
  have hb : base.val ≠ 0 := by
    intro hz
    simp only [hz, Nat.zero_mul] at hov
    omega
  have hap : 1 ≤ acc.val := by omega
  have hpow := square_le_power base.val exp he
  have hacc : base.val ^ exp ≤ acc.val * base.val ^ exp := by
    simpa using Nat.mul_le_mul_right (base.val ^ exp) hap
  exact boundedU128_overflow (lt_of_lt_of_le hov (hpow.trans hacc))

/-- Halving the positive exponent proves termination. The accumulator is
positive unless the base is zero, so an intermediate overflow cannot be
masked by later multiplication by zero. The public call establishes this
invariant from its initial accumulator of one. -/
private theorem checked_pow_loop_agrees (exp : Std.U32) (base acc : Std.U128)
    (hpos : 0 < exp.val) (ha : 0 < acc.val ∨ base.val = 0) :
    CoreSource.core.num.U128.checked_pow_loop exp base acc =
      ok (boundedU128 (acc.val * base.val ^ exp.val)) := by
  obtain ⟨half, hdiv, hhalf⟩ := UScalar.div_spec exp
    (by scalar_tac : (2#u32).val ≠ 0)
  have hh : half.val = exp.val / 2 := by scalar_tac
  have hdecr : half.val < exp.val := by
    rw [hh]
    exact Nat.div_lt_self hpos (by decide)
  rw [CoreSource.core.num.U128.checked_pow_loop, loop]
  by_cases hodd : exp.val % 2 = 1
  · have hbit := (odd_bit exp).mpr hodd
    cases hm : U128.checked_mul acc base with
    | none =>
      have hbound := Nat.mul_le_mul_left acc.val
        (Nat.le_self_pow (n := exp.val) (by omega) base.val)
      have hout := boundedU128_overflow (lt_of_lt_of_le (checked_mul_none hm) hbound)
      simp only [CoreSource.core.num.U128.checked_pow_loop.body,
        lift, bind_tc_ok, if_pos hbit, hm, hout]
    | some product =>
      have hp := checked_mul_some hm
      by_cases hone : exp = 1#u32
      · have he : exp.val = 1 := by scalar_tac
        simp only [CoreSource.core.num.U128.checked_pow_loop.body,
          lift, bind_tc_ok, if_pos hbit, hm, if_pos hone, he, Nat.pow_one,
          ← hp, boundedU128_value]
      · have he : 2 ≤ exp.val := by scalar_tac
        cases hs : U128.checked_mul base base with
        | none =>
          have hout := square_overflow he ha hs
          simp only [CoreSource.core.num.U128.checked_pow_loop.body,
            lift, bind_tc_ok, if_pos hbit, hm, if_neg hone, hdiv, hs, hout]
        | some squared =>
          have hsq := checked_mul_some hs
          have hpositiveHalf : 0 < half.val := by omega
          have hnext : 0 < product.val ∨ squared.val = 0 := by
            by_cases hb : base.val = 0
            · right
              simp only [hsq, hb, Nat.zero_mul]
            · left
              have hap : 0 < acc.val := by omega
              rw [hp]
              exact Nat.mul_pos hap (by omega)
          have hi := checked_pow_loop_agrees half squared product hpositiveHalf hnext
          simp only [CoreSource.core.num.U128.checked_pow_loop.body,
            lift, bind_tc_ok, if_pos hbit, hm, if_neg hone, hdiv, hs]
          change CoreSource.core.num.U128.checked_pow_loop half squared product = _
          rw [hi, hp, hsq, hh, pow_odd base.val exp.val hodd, Nat.mul_assoc]
  · have hbit : ¬ (exp &&& 1#u32) = 1#u32 := by
      simpa only [odd_bit] using hodd
    have heven : exp.val % 2 = 0 := by omega
    have he : 2 ≤ exp.val := by omega
    cases hs : U128.checked_mul base base with
    | none =>
      have hout := square_overflow he ha hs
      simp only [CoreSource.core.num.U128.checked_pow_loop.body,
        lift, bind_tc_ok, if_neg hbit, hdiv, hs, hout]
    | some squared =>
      have hsq := checked_mul_some hs
      have hpositiveHalf : 0 < half.val := by omega
      have hnext : 0 < acc.val ∨ squared.val = 0 := by
        rcases ha with hap | hb
        · exact Or.inl hap
        · right
          simp only [hsq, hb, Nat.zero_mul]
      have hi := checked_pow_loop_agrees half squared acc hpositiveHalf hnext
      simp only [CoreSource.core.num.U128.checked_pow_loop.body,
        lift, bind_tc_ok, if_neg hbit, hdiv, hs]
      change CoreSource.core.num.U128.checked_pow_loop half squared acc = _
      rw [hi, hsq, hh, pow_even base.val exp.val heven]
termination_by exp.val

/-- The actual standard-library squaring loop equals the local mathematical
power model for all bases and exponents, including zero and overflow. No
termination or arithmetic premise is assumed. Checked multiplication remains
an existing Aeneas foundation primitive. -/
theorem core_checked_pow_agrees (value : Std.U128) (exp : Std.U32) :
    CoreSource.core.num.U128.checked_pow value exp =
      core.num.U128.checked_pow value exp := by
  by_cases hz : exp = 0#u32
  · have he : exp.val = 0 := by scalar_tac
    simp only [CoreSource.core.num.U128.checked_pow, if_pos hz,
      core.num.U128.checked_pow, he, Nat.pow_zero]
    have hsmall : 1 < U128.size := by scalar_tac
    rw [if_pos hsmall]
    have hv := boundedU128_value 1#u128
    have hone : (1#u128).val = 1 := by scalar_tac
    simp only [hone, boundedU128, if_pos hsmall] at hv
    exact congrArg ok hv.symm
  · have hpos : 0 < exp.val := by scalar_tac
    have hloop := checked_pow_loop_agrees exp value 1#u128 hpos
      (Or.inl (by scalar_tac))
    simp only [CoreSource.core.num.U128.checked_pow, if_neg hz]
    rw [hloop]
    have hone : (1#u128).val = 1 := by scalar_tac
    simp only [hone, Nat.one_mul, boundedU128, core.num.U128.checked_pow]
    split <;> rfl

#print axioms core_take_agrees
#print axioms core_div_ceil_agrees
#print axioms core_saturating_mul_agrees
#print axioms core_checked_pow_agrees
