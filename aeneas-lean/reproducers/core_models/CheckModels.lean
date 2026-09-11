import Tree.FunsExternal
import CoreSource.Funs

open Aeneas Aeneas.Std Result

/-- The actual Result error adapter preserves successful values without
calling the callback. On error it preserves the callback's exact result,
including failure and divergence, with no callback law or termination premise. -/
theorem core_map_err_agrees {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (value : core.result.Result T E) (op : O) :
    CoreSource.core.result.Result.map_err_source inst value op =
      core.result.Result.map_err inst value op := by
  cases value with
  | Ok _ => rfl
  | Err error =>
    simp only [CoreSource.core.result.Result.map_err_source, core.result.Result.map_err]
    cases inst.call_once op error <;> rfl

/-- The standard-library hint returns its supplied value. This compares the
runtime body; compile-time unused-result diagnostics are outside the model. -/
theorem core_must_use_agrees {T : Type} (value : T) :
    CoreSource.core.hint.must_use value = core.hint.must_use value := rfl

/-- Blanket borrowing agrees with the local identity model in Aeneas's
reference/value abstraction. No element clone or Borrow dictionary is assumed. -/
theorem core_borrow_agrees {T : Type} (value : T) :
    CoreSource.core.borrow.Borrow.Blanket.borrow value =
      core.borrow.Borrow.Blanket.borrow value := rfl

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
    CoreSource.core.num.U128.checked_pow_loop1 exp base acc =
      ok (boundedU128 (acc.val * base.val ^ exp.val)) := by
  obtain ⟨half, hdiv, hhalf⟩ := UScalar.div_spec exp
    (by scalar_tac : (2#u32).val ≠ 0)
  have hh : half.val = exp.val / 2 := by scalar_tac
  have hdecr : half.val < exp.val := by
    rw [hh]
    exact Nat.div_lt_self hpos (by decide)
  rw [CoreSource.core.num.U128.checked_pow_loop1, loop]
  by_cases hodd : exp.val % 2 = 1
  · have hbit := (odd_bit exp).mpr hodd
    cases hm : U128.checked_mul acc base with
    | none =>
      have hbound := Nat.mul_le_mul_left acc.val
        (Nat.le_self_pow (n := exp.val) (by omega) base.val)
      have hout := boundedU128_overflow (lt_of_lt_of_le (checked_mul_none hm) hbound)
      simp only [CoreSource.core.num.U128.checked_pow_loop1.body,
        lift, bind_tc_ok, if_pos hbit, hm, hout]
    | some product =>
      have hp := checked_mul_some hm
      by_cases hone : exp = 1#u32
      · have he : exp.val = 1 := by scalar_tac
        simp only [CoreSource.core.num.U128.checked_pow_loop1.body,
          lift, bind_tc_ok, if_pos hbit, hm, if_pos hone, he, Nat.pow_one,
          ← hp, boundedU128_value]
      · have he : 2 ≤ exp.val := by scalar_tac
        cases hs : U128.checked_mul base base with
        | none =>
          have hout := square_overflow he ha hs
          simp only [CoreSource.core.num.U128.checked_pow_loop1.body,
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
          simp only [CoreSource.core.num.U128.checked_pow_loop1.body,
            lift, bind_tc_ok, if_pos hbit, hm, if_neg hone, hdiv, hs]
          change CoreSource.core.num.U128.checked_pow_loop1 half squared product = _
          rw [hi, hp, hsq, hh, pow_odd base.val exp.val hodd, Nat.mul_assoc]
  · have hbit : ¬ (exp &&& 1#u32) = 1#u32 := by
      simpa only [odd_bit] using hodd
    have heven : exp.val % 2 = 0 := by omega
    have he : 2 ≤ exp.val := by omega
    cases hs : U128.checked_mul base base with
    | none =>
      have hout := square_overflow he ha hs
      simp only [CoreSource.core.num.U128.checked_pow_loop1.body,
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
      simp only [CoreSource.core.num.U128.checked_pow_loop1.body,
        lift, bind_tc_ok, if_neg hbit, hdiv, hs]
      change CoreSource.core.num.U128.checked_pow_loop1 half squared acc = _
      rw [hi, hsq, hh, pow_even base.val exp.val heven]
termination_by exp.val

/-- Both compiler-selected loops implement the same checked computation. -/
private theorem checked_pow_loops_agree (exp : Std.U32) (base acc : Std.U128)
    (hpos : 0 < exp.val) :
    CoreSource.core.num.U128.checked_pow_loop0 exp base acc =
      CoreSource.core.num.U128.checked_pow_loop1 exp base acc := by
  obtain ⟨half, hdiv, hhalf⟩ := UScalar.div_spec exp
    (by scalar_tac : (2#u32).val ≠ 0)
  have hh : half.val = exp.val / 2 := by scalar_tac
  have hdecr : half.val < exp.val := by
    rw [hh]
    exact Nat.div_lt_self hpos (by decide)
  simp only [CoreSource.core.num.U128.checked_pow_loop0,
    CoreSource.core.num.U128.checked_pow_loop1]
  rw [loop, loop]
  by_cases hone : exp = 1#u32
  · subst exp
    simp [CoreSource.core.num.U128.checked_pow_loop0.body,
      CoreSource.core.num.U128.checked_pow_loop1.body, lift]
    cases U128.checked_mul acc base <;> rfl
  · have hgt : exp > 1#u32 := by scalar_tac
    have hhalfPos : 0 < half.val := by scalar_tac
    simp only [CoreSource.core.num.U128.checked_pow_loop0.body,
      CoreSource.core.num.U128.checked_pow_loop1.body, if_pos hgt, if_neg hone,
      lift, bind_tc_ok]
    by_cases hodd : exp &&& 1#u32 = 1#u32
    · simp only [if_pos hodd]
      cases hm : U128.checked_mul acc base with
      | none => simp [hm]
      | some product =>
        cases hs : U128.checked_mul base base with
        | none => simp [hm, hdiv, hs]
        | some squared =>
          simp only [hm, hdiv, hs, bind_tc_ok]
          change CoreSource.core.num.U128.checked_pow_loop0 half squared product = _
          exact checked_pow_loops_agree half squared product hhalfPos
    · simp only [if_neg hodd]
      cases hs : U128.checked_mul base base with
      | none => simp [hdiv, hs]
      | some squared =>
        simp only [hdiv, hs, bind_tc_ok]
        change CoreSource.core.num.U128.checked_pow_loop0 half squared acc = _
        exact checked_pow_loops_agree half squared acc hhalfPos
termination_by exp.val

private theorem bounded_power_two (shift : Nat) :
    boundedU128 (2 ^ shift) =
      if shift < 128 then some ⟨BitVec.ofNat 128 (2 ^ shift)⟩ else none := by
  have hbound : 2 ^ shift < U128.size ↔ shift < 128 := by
    simp only [U128.size, U128.numBits, UScalarTy.numBits]
    exact Nat.pow_lt_pow_iff_right (by decide)
  simp only [boundedU128, hbound, UScalarTy.numBits]

private theorem checked_shl_one_agrees (shift : Std.U32) :
    core.num.U128.checked_shl 1#u128 shift = ok (boundedU128 (2 ^ shift.val)) := by
  rw [bounded_power_two]
  have hone : (1#u128).val = 1 := by scalar_tac
  simp only [core.num.U128.checked_shl, milhouse.numeric.checked_shl, hone, Nat.one_mul, UScalarTy.numBits]
  split <;> simp_all

/-- The new power-of-two shortcut returns the same bounded mathematical
power, including multiplication overflow when calculating the shift. -/
private theorem optimized_power_agrees (value : Std.U128) (exp : Std.U32)
    (hpower : value.val.isPowerOfTwo) :
    (do let k ← core.num.U128.ilog2 value
        let shift ← lift (U32.checked_mul k exp)
        match shift with
        | none => ok none
        | some shift => core.num.U128.checked_shl 1#u128 shift) =
      ok (boundedU128 (value.val ^ exp.val)) := by
  obtain ⟨k, hkvalue⟩ := hpower
  have hk : k < 128 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hkvalue]
    scalar_tac
  let k32 : Std.U32 := ⟨BitVec.ofNat 32 k⟩
  have hk32 : k32.val = k := by
    simp [k32, UScalar.val] <;> omega
  have hmk : UScalar.tryMk .U32 k32.val = ok k32 := by
    simp only [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, k32.hBounds,
      decide_true, ↓reduceDIte, Result.ofOption]
    congr 1
  have hnonzero : value.val ≠ 0 := by simp [hkvalue]
  have hlog : core.num.U128.ilog2 value = ok k32 := by
    rw [core.num.U128.ilog2, milhouse.numeric.ilog2, if_neg hnonzero,
      hkvalue, Nat.log2_two_pow, ← hk32]
    exact hmk
  simp only [hlog, bind_tc_ok, lift]
  cases hm : U32.checked_mul k32 exp with
  | none =>
    have hmul := U32.checked_mul_bv_spec k32 exp
    simp only [hm, hk32] at hmul
    have hlarge : 128 ≤ k * exp.val := by scalar_tac
    rw [hkvalue, ← Nat.pow_mul, bounded_power_two, if_neg (by omega)]
  | some shift =>
    have hmul := U32.checked_mul_bv_spec k32 exp
    simp only [hm, hk32] at hmul
    simp only [bind_tc_ok]
    rw [checked_shl_one_agrees, hmul.2.1, hkvalue, ← Nat.pow_mul]

/-- Every compiler-selector outcome agrees with the local mathematical
power model, including the new power-of-two shortcut and both loop forms.
No input bound, termination assumption, or relationship between selector
outcomes is required. Numeric helper foundations are explicit in the audit. -/
theorem core_checked_pow_agrees [milhouse.compiler.StaticKnown]
    (value : Std.U128) (exp : Std.U32) :
    CoreSource.core.num.U128.checked_pow value exp =
      core.num.U128.checked_pow value exp := by
  have hmodel : core.num.U128.checked_pow value exp =
      ok (boundedU128 (value.val ^ exp.val)) := by
    simp! only [core.num.U128.checked_pow, boundedU128]
    split <;> simp_all
  rw [hmodel]
  have hdefault (choice : Bool) :
      (if exp = 0#u32 then ok (some 1#u128)
       else if choice then CoreSource.core.num.U128.checked_pow_loop0 exp value 1#u128
       else CoreSource.core.num.U128.checked_pow_loop1 exp value 1#u128) =
      ok (boundedU128 (value.val ^ exp.val)) := by
    by_cases hz : exp = 0#u32
    · have he : exp.val = 0 := by scalar_tac
      have hone : (1#u128).val = 1 := by scalar_tac
      simp only [if_pos hz, he, Nat.pow_zero]
      exact congrArg ok (by simpa only [hone] using (boundedU128_value 1#u128).symm)
    · have hpos : 0 < exp.val := by scalar_tac
      have hloop := checked_pow_loop_agrees exp value 1#u128 hpos
        (Or.inl (by scalar_tac))
      have hone : (1#u128).val = 1 := by scalar_tac
      simp only [hone, Nat.one_mul] at hloop
      simp only [if_neg hz, checked_pow_loops_agree exp value 1#u128 hpos]
      cases choice <;> exact hloop
  have hloop2 : CoreSource.core.num.U128.checked_pow_loop2 =
      CoreSource.core.num.U128.checked_pow_loop0 := rfl
  have hloop3 : CoreSource.core.num.U128.checked_pow_loop3 =
      CoreSource.core.num.U128.checked_pow_loop1 := rfl
  simp only [CoreSource.core.num.U128.checked_pow, hloop2, hloop3,
    core.intrinsics.is_val_statically_known, bind_tc_ok,
    core.num.U128.is_power_of_two, decide_eq_true_eq]
  split
  · split
    · rename_i hpower
      exact optimized_power_agrees value exp hpower
    · exact hdefault _
  · exact hdefault _

#print axioms core_take_agrees
#print axioms core_div_ceil_agrees
#print axioms core_saturating_mul_agrees
#print axioms core_checked_pow_agrees
#print axioms core_map_err_agrees
#print axioms core_must_use_agrees
#print axioms core_borrow_agrees
