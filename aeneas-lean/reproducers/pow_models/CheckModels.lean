import Tree.FunsExternal
import PowSource.Funs

open Aeneas Aeneas.Std Result

private theorem tryMk_value (value : Std.Usize) :
    UScalar.tryMk .Usize value.val = ok value := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, value.hBounds,
    decide_true, ↓reduceDIte, Result.ofOption]
  congr 1

private theorem tryMk_overflow {n : Nat} (h : Std.Usize.max < n) :
    UScalar.tryMk .Usize n = fail Error.integerOverflow := by
  have hn : ¬ n < 2 ^ System.Platform.numBits := by scalar_tac
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, hn, Result.ofOption]

private theorem mul_cases (left right : Std.Usize) :
    (∃ product, left * right = ok product ∧ product.val = left.val * right.val) ∨
    (left * right = fail Error.integerOverflow ∧ Std.Usize.max < left.val * right.val) := by
  by_cases h : left.val * right.val ≤ Std.Usize.max
  · obtain ⟨product, hm, hp⟩ := WP.spec_imp_exists
      (UScalar.mul_bv_spec (x := left) (y := right) (by scalar_tac))
    exact Or.inl ⟨product, hm, hp.1⟩
  · exact Or.inr ⟨tryMk_overflow (by omega), by omega⟩

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

private theorem square_overflow {base acc : Std.Usize} {exp : Nat}
    (he : 2 ≤ exp) (ha : 0 < acc.val ∨ base.val = 0)
    (hov : Std.Usize.max < base.val * base.val) :
    UScalar.tryMk .Usize (acc.val * base.val ^ exp) = fail Error.integerOverflow := by
  have hb : base.val ≠ 0 := by
    intro hz
    simp only [hz, Nat.zero_mul] at hov
    omega
  have hap : 1 ≤ acc.val := by omega
  have hpow := square_le_power base.val exp he
  have hacc : base.val ^ exp ≤ acc.val * base.val ^ exp := by
    simpa using Nat.mul_le_mul_right (base.val ^ exp) hap
  exact tryMk_overflow (lt_of_lt_of_le hov (hpow.trans hacc))

/-- The dynamic-exponent loop terminates by halving its positive exponent.
The accumulator invariant prevents later multiplication by zero from hiding
an earlier overflow. It holds initially for every base, including zero. -/
private theorem pow_loop1_agrees (exp : Std.U32) (base acc : Std.Usize)
    (hpos : 0 < exp.val) (ha : 0 < acc.val ∨ base.val = 0) :
    PowSource.core.num.Usize.pow_loop1 exp base acc =
      UScalar.tryMk .Usize (acc.val * base.val ^ exp.val) := by
  obtain ⟨half, hdiv, hhalf⟩ := UScalar.div_spec exp
    (by scalar_tac : (2#u32).val ≠ 0)
  have hh : half.val = exp.val / 2 := by scalar_tac
  have hdecr : half.val < exp.val := by
    rw [hh]
    exact Nat.div_lt_self hpos (by decide)
  rw [PowSource.core.num.Usize.pow_loop1, loop]
  by_cases hodd : exp.val % 2 = 1
  · have hbit := (odd_bit exp).mpr hodd
    rcases mul_cases acc base with ⟨product, hm, hp⟩ | ⟨hm, hov⟩
    · by_cases hone : exp = 1#u32
      · have he : exp.val = 1 := by scalar_tac
        simp only [PowSource.core.num.Usize.pow_loop1.body,
          lift, bind_tc_ok, if_pos hbit, hm, if_pos hone, he, Nat.pow_one,
          ← hp, tryMk_value]
      · have he : 2 ≤ exp.val := by scalar_tac
        rcases mul_cases base base with ⟨squared, hs, hsq⟩ | ⟨hs, hsov⟩
        · have hpositiveHalf : 0 < half.val := by omega
          have hnext : 0 < product.val ∨ squared.val = 0 := by
            by_cases hb : base.val = 0
            · right
              simp only [hsq, hb, Nat.zero_mul]
            · left
              have hap : 0 < acc.val := by omega
              rw [hp]
              exact Nat.mul_pos hap (by omega)
          have hi := pow_loop1_agrees half squared product hpositiveHalf hnext
          simp only [PowSource.core.num.Usize.pow_loop1.body,
            lift, bind_tc_ok, if_pos hbit, hm, if_neg hone, hdiv, hs]
          change PowSource.core.num.Usize.pow_loop1 half squared product = _
          rw [hi, hp, hsq, hh, pow_odd base.val exp.val hodd, Nat.mul_assoc]
        · have hout := square_overflow he ha hsov
          simp only [PowSource.core.num.Usize.pow_loop1.body,
            lift, bind_tc_ok, bind_tc_fail, if_pos hbit, hm, if_neg hone, hdiv, hs, hout]
    · have hbound := Nat.mul_le_mul_left acc.val
        (Nat.le_self_pow (n := exp.val) (by omega) base.val)
      have hout := tryMk_overflow (lt_of_lt_of_le hov hbound)
      simp only [PowSource.core.num.Usize.pow_loop1.body,
        lift, bind_tc_ok, bind_tc_fail, if_pos hbit, hm, hout]
  · have hbit : ¬ (exp &&& 1#u32) = 1#u32 := by
      simpa only [odd_bit] using hodd
    have heven : exp.val % 2 = 0 := by omega
    have he : 2 ≤ exp.val := by omega
    rcases mul_cases base base with ⟨squared, hs, hsq⟩ | ⟨hs, hsov⟩
    · have hpositiveHalf : 0 < half.val := by omega
      have hnext : 0 < acc.val ∨ squared.val = 0 := by
        rcases ha with hap | hb
        · exact Or.inl hap
        · right
          simp only [hsq, hb, Nat.zero_mul]
      have hi := pow_loop1_agrees half squared acc hpositiveHalf hnext
      simp only [PowSource.core.num.Usize.pow_loop1.body,
        lift, bind_tc_ok, if_neg hbit, hdiv, hs]
      change PowSource.core.num.Usize.pow_loop1 half squared acc = _
      rw [hi, hsq, hh, pow_even base.val exp.val heven]
    · have hout := square_overflow he ha hsov
      simp only [PowSource.core.num.Usize.pow_loop1.body,
        lift, bind_tc_ok, bind_tc_fail, if_neg hbit, hdiv, hs, hout]
termination_by exp.val


/-- The constant-exponent loop followed by its final multiplication has the
same result as the dynamic-exponent loop. This includes every multiplication
failure and requires no bound on the base or accumulator. -/
private theorem pow_loops_agree (exp : Std.U32) (base acc : Std.Usize)
    (hpos : 0 < exp.val) :
    (do
      let (base', acc') ← PowSource.core.num.Usize.pow_loop0 exp base acc
      acc' * base') = PowSource.core.num.Usize.pow_loop1 exp base acc := by
  obtain ⟨half, hdiv, hhalf⟩ := UScalar.div_spec exp
    (by scalar_tac : (2#u32).val ≠ 0)
  have hh : half.val = exp.val / 2 := by scalar_tac
  have hdecr : half.val < exp.val := by
    rw [hh]
    exact Nat.div_lt_self hpos (by decide)
  conv_lhs => rw [PowSource.core.num.Usize.pow_loop0, loop]
  conv_rhs => rw [PowSource.core.num.Usize.pow_loop1, loop]
  by_cases hone : exp = 1#u32
  · have hnot : ¬ exp > 1#u32 := by scalar_tac
    have hbit : (exp &&& 1#u32) = 1#u32 := by
      rw [odd_bit]
      have he : exp.val = 1 := by scalar_tac
      simp only [he, Nat.mod_succ]
    cases hm : acc * base <;>
      simp only [lift, bind_tc_ok, bind_tc_fail, bind_tc_div,
        PowSource.core.num.Usize.pow_loop0.body,
        PowSource.core.num.Usize.pow_loop1.body, if_neg hnot, if_pos hbit, if_pos hone, hm] <;> exact hm
  · have hgt : exp > 1#u32 := by scalar_tac
    have hpositiveHalf : 0 < half.val := by scalar_tac
    by_cases hbit : (exp &&& 1#u32) = 1#u32
    · cases hm : acc * base with
      | fail error =>
        simp only [lift, bind_tc_ok, bind_tc_fail,
          PowSource.core.num.Usize.pow_loop0.body,
          PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, if_pos hbit, hm]
      | div =>
        simp only [lift, bind_tc_ok, bind_tc_div,
          PowSource.core.num.Usize.pow_loop0.body,
          PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, if_pos hbit, hm]
      | ok product =>
        cases hs : base * base with
        | fail error =>
          simp only [lift, bind_tc_ok, bind_tc_fail,
            PowSource.core.num.Usize.pow_loop0.body,
            PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, if_pos hbit, hm, if_neg hone, hdiv, hs]
        | div =>
          simp only [lift, bind_tc_ok, bind_tc_div,
            PowSource.core.num.Usize.pow_loop0.body,
            PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, if_pos hbit, hm, if_neg hone, hdiv, hs]
        | ok squared =>
          simp only [PowSource.core.num.Usize.pow_loop0.body,
            PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, lift, bind_tc_ok,
            if_pos hbit, hm, if_neg hone, hdiv, hs]
          change (do
            let (base', acc') ← PowSource.core.num.Usize.pow_loop0 half squared product
            acc' * base') = PowSource.core.num.Usize.pow_loop1 half squared product
          exact pow_loops_agree half squared product hpositiveHalf
    · cases hs : base * base with
      | fail error =>
        simp only [lift, bind_tc_ok, bind_tc_fail,
          PowSource.core.num.Usize.pow_loop0.body,
          PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, if_neg hbit, hdiv, hs]
      | div =>
        simp only [lift, bind_tc_ok, bind_tc_div,
          PowSource.core.num.Usize.pow_loop0.body,
          PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, if_neg hbit, hdiv, hs]
      | ok squared =>
        simp only [PowSource.core.num.Usize.pow_loop0.body,
          PowSource.core.num.Usize.pow_loop1.body, if_pos hgt, lift, bind_tc_ok,
          if_neg hbit, hdiv, hs]
        change (do
          let (base', acc') ← PowSource.core.num.Usize.pow_loop0 half squared acc
          acc' * base') = PowSource.core.num.Usize.pow_loop1 half squared acc
        exact pow_loops_agree half squared acc hpositiveHalf
termination_by exp.val

/-- For either permitted compiler-selector outcome, the entire pinned Rust
power body agrees with the local model on every base and exponent. Both
extracted loops, exponent zero, and exact overflow failure are included.
Only the selector and existing Aeneas scalar primitives are abstracted. -/
theorem core_pow_agrees [PowSource.StaticKnown] (value : Std.Usize) (exp : Std.U32) :
    PowSource.core.num.Usize.pow value exp = core.num.Usize.pow value exp := by
  by_cases hz : exp = 0#u32
  · have he : exp.val = 0 := by scalar_tac
    simp only [PowSource.core.num.Usize.pow, if_pos hz, core.num.Usize.pow,
      he, Nat.pow_zero]
    have hone : (1#usize).val = 1 := by scalar_tac
    exact (hone ▸ tryMk_value 1#usize).symm
  · have hpos : 0 < exp.val := by scalar_tac
    have hloop := pow_loop1_agrees exp value 1#usize hpos (Or.inl (by scalar_tac))
    simp only [PowSource.core.num.Usize.pow, if_neg hz,
      core.intrinsics.is_val_statically_known, bind_tc_ok, core.num.Usize.pow]
    split
    · rw [pow_loops_agree exp value 1#usize hpos, hloop]
      have hone : (1#usize).val = 1 := by scalar_tac
      rw [hone, Nat.one_mul]
    · rw [hloop]
      have hone : (1#usize).val = 1 := by scalar_tac
      rw [hone, Nat.one_mul]

#print axioms core_pow_agrees
