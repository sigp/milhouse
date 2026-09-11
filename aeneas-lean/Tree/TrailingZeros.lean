import Tree.Funs
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Aeneas Aeneas.Std Result

namespace milhouse.tree

private theorem natTrailingZeros_eq_padicValNat :
    ∀ fuel n : Nat, 0 < n → padicValNat 2 n ≤ fuel →
      TreeAux.natTrailingZeros fuel n = padicValNat 2 n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hbound
    have hzero : padicValNat 2 n = 0 := by omega
    simp [TreeAux.natTrailingZeros, hzero]
  | succ fuel ih =>
    intro n hn hbound
    unfold TreeAux.natTrailingZeros
    by_cases heven : n % 2 = 0
    · rw [if_pos heven]
      have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
      have hn_two : 2 ≤ n := Nat.le_of_dvd hn hdvd
      have hdiv_pos : 0 < n / 2 := Nat.div_pos hn_two (by omega)
      have hval_ne : padicValNat 2 n ≠ 0 :=
        (dvd_iff_padicValNat_ne_zero (p := 2) hn.ne').mp hdvd
      have hdiv_val := padicValNat.div (p := 2) hdvd
      rw [ih (n / 2) hdiv_pos (by omega), hdiv_val]
      omega
    · rw [if_neg heven]
      have hnot_dvd : ¬2 ∣ n := by
        intro hdvd
        exact heven (Nat.mod_eq_zero_of_dvd hdvd)
      rw [padicValNat.eq_zero_of_not_dvd hnot_dvd]

private theorem natTrailingZeros_le_fuel :
    ∀ fuel n : Nat, TreeAux.natTrailingZeros fuel n ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro n; simp [TreeAux.natTrailingZeros]
  | succ fuel ih =>
    intro n
    unfold TreeAux.natTrailingZeros
    split
    · have := ih (n / 2)
      omega
    · omega

/-- Rust's trailing-zero result on a positive word is its exact power-of-two
    valuation. Shared by builder carry and iterator backtracking proofs. -/
theorem usize_trailing_zeros_padic {value : Std.Usize} {zeros : Std.U32}
    (hvalue : 0 < value.val)
    (hzeros : core.num.Usize.trailing_zeros value = ok zeros) :
    zeros.val = padicValNat 2 value.val := by
  have hbv : value.bv ≠ 0 := by
    intro hzero
    have hval_zero : value.val = 0 := by
      change value.bv.toNat = 0
      rw [hzero]
      rfl
    omega
  have htz_le := natTrailingZeros_le_fuel System.Platform.numBits value.val
  have hpadic_le : padicValNat 2 value.val ≤ System.Platform.numBits := by
    have hpow_le : 2 ^ padicValNat 2 value.val ≤ value.val :=
      Nat.le_of_dvd hvalue pow_padicValNat_dvd
    by_contra hnot_le
    have hpow_lt : 2 ^ System.Platform.numBits <
        2 ^ padicValNat 2 value.val :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hbits : value.val < 2 ^ System.Platform.numBits := by
      simpa using value.hBounds
    omega
  unfold core.num.Usize.trailing_zeros at hzeros
  have hzero_eq : zeros =
      ⟨BitVec.ofNat 32 (TreeAux.bvTrailingZeros value.bv)⟩ := by
    injection hzeros with heq
    exact heq.symm
  subst zeros
  change (BitVec.ofNat 32 (TreeAux.bvTrailingZeros value.bv)).toNat =
    padicValNat 2 value.val
  unfold TreeAux.bvTrailingZeros
  rw [if_neg hbv]
  change (BitVec.ofNat 32
    (TreeAux.natTrailingZeros System.Platform.numBits value.val)).toNat =
      padicValNat 2 value.val
  rw [natTrailingZeros_eq_padicValNat System.Platform.numBits value.val
    hvalue hpadic_le]
  simp only [BitVec.toNat_ofNat]
  have hword : System.Platform.numBits < 2 ^ 32 := by
    have := System.Platform.numBits_le
    omega
  have : padicValNat 2 value.val < 2 ^ 32 := by omega
  exact Nat.mod_eq_of_lt this

end milhouse.tree
