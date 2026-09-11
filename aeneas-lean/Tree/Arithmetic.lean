import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Checked `Usize` addition succeeds when its mathematical sum is the value
    of an existing `Usize`. -/
theorem usize_add_eq_of_val {x y z : Std.Usize}
    (hval : x.val + y.val = z.val) : x + y = ok z := by
  have hadd := UScalar.add_equiv x y
  cases heq : x + y with
  | fail e =>
    rw [heq] at hadd
    simp at hadd
    have hzbound : z.val < 2 ^ System.Platform.numBits := by
      simpa using z.hBounds
    omega
  | div =>
    rw [heq] at hadd
    simp at hadd
  | ok result =>
    rw [heq] at hadd
    simp at hadd
    have hresult : result = z := by scalar_tac
    exact congrArg ok hresult

theorem usize_add_zero_eq (x : Std.Usize) : x + 0#usize = ok x :=
  usize_add_eq_of_val (by simp)

/-- Successful checked addition agrees with natural-number addition. -/
theorem usize_add_val {x y sum : Std.Usize}
    (h : x + y = ok sum) : sum.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  rw [h] at hadd
  simp at hadd
  omega

/-- Successful subtraction by one exposes the predecessor relation. -/
theorem usize_sub_one_val {x predecessor : Std.Usize}
    (h : x - 1#usize = ok predecessor) :
    x.val = predecessor.val + 1 := by
  have hsub := UScalar.sub_equiv x 1#usize
  rw [h] at hsub
  obtain ⟨-, hone, -⟩ := hsub
  scalar_tac

/-- Successful right shift agrees with `Nat.shiftRight`. -/
theorem usize_shift_right_val {x shift shifted : Std.Usize}
    (h : x >>> shift = ok shifted) :
    shifted.val = x.val >>> shift.val := by
  have hbound : shift.val < System.Platform.numBits := by
    change UScalar.shiftRight x shift.val = ok shifted at h
    unfold UScalar.shiftRight at h
    split at h
    · assumption
    · simp at h
  have hspec := Std.Usize.ShiftRight_spec x shift hbound
  rw [h] at hspec
  exact hspec.1

/-- Testing routing bit `shift` selects the lower half exactly when the index
    modulo the represented parent capacity lies below the child capacity. -/
theorem routing_bit_zero_iff {index shift shifted : Std.Usize}
    (hshift : index >>> shift = ok shifted) :
    (shifted &&& 1#usize) = 0#usize ↔
      index.val % (2 ^ (shift.val + 1)) < 2 ^ shift.val := by
  have hshifted := usize_shift_right_val hshift
  have hnat :
      ((index.val >>> shift.val) &&& 1 = 0) ↔
        index.val % (2 ^ (shift.val + 1)) < 2 ^ shift.val := by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, pow_succ]
    rw [← Nat.mod_mul_right_div_self]
    exact Nat.div_eq_zero_iff_lt (Nat.two_pow_pos shift.val)
  constructor
  · intro hbit
    apply hnat.mp
    have hbitval := congrArg UScalar.val hbit
    simpa [hshifted] using hbitval
  · intro hleft
    have hbitval := hnat.mpr hleft
    apply UScalar.eq_of_val_eq
    simpa [hshifted] using hbitval

/-- Reducing modulo a child capacity after the parent capacity changes
    nothing when the parent remainder selects the left child. -/
theorem mod_child_eq_parent_of_lt (index child_capacity : Nat)
    (hleft : index % (child_capacity * 2) < child_capacity) :
    index % child_capacity = index % (child_capacity * 2) := by
  calc
    index % child_capacity =
        (index % (child_capacity * 2)) % child_capacity := by
          symm
          exact Nat.mod_mul_right_mod index child_capacity 2
    _ = index % (child_capacity * 2) := Nat.mod_eq_of_lt hleft

/-- In the right half, reducing modulo the child capacity subtracts exactly
    one child capacity from the parent remainder. -/
theorem mod_child_eq_parent_sub_of_not_lt (index child_capacity : Nat)
    (hchild : 0 < child_capacity)
    (hright : ¬ index % (child_capacity * 2) < child_capacity) :
    index % child_capacity =
      index % (child_capacity * 2) - child_capacity := by
  let remainder := index % (child_capacity * 2)
  have hremainder_lt : remainder < child_capacity * 2 :=
    Nat.mod_lt index (by omega)
  have hremainder_ge : child_capacity ≤ remainder := by omega
  calc
    index % child_capacity = remainder % child_capacity := by
      exact (Nat.mod_mul_right_mod index child_capacity 2).symm
    _ = (remainder - child_capacity) % child_capacity :=
      Nat.mod_eq_sub_mod hremainder_ge
    _ = remainder - child_capacity := Nat.mod_eq_of_lt (by omega)

/-- A natural-number remainder of zero yields the corresponding successful
    translated `Usize` operation. -/
theorem usize_rem_eq_zero {index factor : Std.Usize}
    (hfactor : 0 < factor.val) (hrem : index.val % factor.val = 0) :
    index % factor = ok 0#usize := by
  have hspec := Std.Usize.rem_bv_spec index (Nat.ne_of_gt hfactor)
  cases heq : index % factor with
  | fail e => rw [heq] at hspec; simp at hspec
  | div => rw [heq] at hspec; simp at hspec
  | ok remainder =>
    rw [heq] at hspec
    have hremainder : remainder = 0#usize := by
      have := hspec.1
      scalar_tac
    exact congrArg ok hremainder


/-- Subtraction of one from a positive `Usize` succeeds. -/
theorem usize_sub_one_succeeds {x : Std.Usize} (h : 0 < x.val) :
    ∃ predecessor, x - 1#usize = ok predecessor ∧
      x.val = predecessor.val + 1 := by
  have hsub := UScalar.sub_equiv x 1#usize
  cases heq : x - 1#usize with
  | fail e => rw [heq] at hsub; scalar_tac
  | div => rw [heq] at hsub; simp at hsub
  | ok predecessor =>
    rw [heq] at hsub
    obtain ⟨-, hval, -⟩ := hsub
    exact ⟨predecessor, rfl, by scalar_tac⟩

/-- Addition succeeds when the mathematical sum stays in bounds. -/
theorem usize_add_succeeds {x y : Std.Usize}
    (h : x.val + y.val < 2 ^ System.Platform.numBits) :
    ∃ sum, x + y = ok sum ∧ sum.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  cases heq : x + y with
  | fail e => rw [heq] at hadd; simp at hadd; scalar_tac
  | div => rw [heq] at hadd; simp at hadd
  | ok sum =>
    rw [heq] at hadd
    simp at hadd
    exact ⟨sum, rfl, by omega⟩

/-- Right shift succeeds for shift amounts below the word size. -/
theorem usize_shift_right_succeeds (x : Std.Usize)
    {shift : Std.Usize} (h : shift.val < System.Platform.numBits) :
    ∃ shifted, x >>> shift = ok shifted ∧
      shifted.val = x.val >>> shift.val := by
  have hspec := Std.Usize.ShiftRight_spec x shift h
  cases heq : x >>> shift with
  | fail e => rw [heq] at hspec; simp at hspec
  | div => rw [heq] at hspec; simp at hspec
  | ok shifted =>
    rw [heq] at hspec
    exact ⟨shifted, rfl, hspec.1⟩

/-- Remainder by a positive divisor succeeds. -/
theorem usize_rem_succeeds (x : Std.Usize) {factor : Std.Usize}
    (h : 0 < factor.val) :
    ∃ remainder, x % factor = ok remainder ∧
      remainder.val = x.val % factor.val := by
  have hspec := Std.Usize.rem_bv_spec x (Nat.ne_of_gt h)
  cases heq : x % factor with
  | fail e => rw [heq] at hspec; simp at hspec
  | div => rw [heq] at hspec; simp at hspec
  | ok remainder =>
    rw [heq] at hspec
    exact ⟨remainder, rfl, hspec.1⟩


/-- Setting a single clear bit is addition: `a ||| 2^s = a + 2^s` when `a`
    is aligned past bit `s`. Bridges the translated `prefix | (1 << shift)`
    to the arithmetic form used by the dense split. -/
theorem or_two_pow_aligned {a s : Nat} (h : a % 2 ^ (s + 1) = 0) :
    a ||| 2 ^ s = a + 2 ^ s := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  apply Nat.eq_of_testBit_eq
  intro i
  have hsum : 2 ^ (s + 1) * q + 2 ^ s = (2 * q + 1) <<< s := by
    rw [Nat.shiftLeft_eq]
    ring
  have hshift : 2 ^ (s + 1) * q = q <<< (s + 1) := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hsum, hshift]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i s with hlt | heq | hgt
  · have h1 : ¬ (s + 1 ≤ i) := by omega
    have h2 : ¬ (s ≤ i) := by omega
    have h3 : ¬ (s = i) := by omega
    simp [h1, h2, h3]
  · subst heq
    have h1 : ¬ (i + 1 ≤ i) := by omega
    simp [h1, Nat.testBit_zero]
    try omega
  · have h1 : s + 1 ≤ i := by omega
    have h2 : s ≤ i := by omega
    have h3 : ¬ (s = i) := by omega
    simp only [h1, h2, h3, decide_true, decide_false, Bool.true_and,
      Bool.or_false]
    obtain ⟨j, hj⟩ : ∃ j, i - s = j + 1 := ⟨i - s - 1, by omega⟩
    rw [hj, Nat.testBit_add_one]
    have hdiv : (2 * q + 1) / 2 = q := by omega
    rw [hdiv]
    congr 1
    omega

/-- Bitwise-or on `Usize` is bitwise-or of the values. -/
theorem usize_or_val (x y : Std.Usize) :
    (x ||| y).val = x.val ||| y.val := by
  show (UScalar.or x y).val = x.val ||| y.val
  simp only [UScalar.or, UScalar.val]
  simp [BitVec.toNat_or]

/-- Alignment descends to the half capacity. -/
theorem mod_half_eq_zero {p h : Nat} (hp : p % (h * 2) = 0) :
    p % h = 0 :=
  Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans ⟨2, rfl⟩ (Nat.dvd_of_mod_eq_zero hp))

/-- A successful `1 << shift` is exactly the power of two. -/
theorem usize_shift_left_one_val {shift shifted : Std.Usize}
    (h : 1#usize <<< shift = ok shifted) :
    shifted.val = 2 ^ shift.val := by
  have hbound : shift.val < UScalarTy.Usize.numBits := by
    change UScalar.shiftLeft 1#usize shift.val = ok shifted at h
    unfold UScalar.shiftLeft at h
    split at h
    · assumption
    · simp at h
  have hspec := UScalar.ShiftLeft_spec 1#usize shift
    (UScalar.size UScalarTy.Usize) hbound rfl
  rw [h] at hspec
  obtain ⟨hval, -⟩ := hspec
  have hone : (1#usize).val = 1 := by simp
  rw [hval, hone, Nat.one_shiftLeft, UScalar.size_def]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hbound)

/-- Within one aligned window, reduction modulo its width subtracts exactly
    the window start. The bounds already imply a positive width. -/
theorem mod_eq_sub_of_aligned {start width index : Nat}
    (halign : start % width = 0) (hlo : start ≤ index) (hhi : index < start + width) :
    index % width = index - start := by
  have hindex : index = start + (index - start) := by omega
  calc
    index % width = (start + (index - start)) % width := congrArg (· % width) hindex
    _ = (index - start) % width := by simp [Nat.add_mod, halign]
    _ = index - start := Nat.mod_eq_of_lt (by omega)

end milhouse.tree
