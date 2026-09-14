import Tree.ProgressiveTree.Depth
import Tree.Arithmetic

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

theorem prog_tree_exponent_cast : UScalar.cast .U128 PROG_TREE_EXPONENT = 4#u128 := by
  apply UScalar.eq_of_val_eq
  simp [PROG_TREE_EXPONENT, UScalar.cast_val_eq]

/-- Checked exponentiation with the Rust maximum-value fallback is exactly
    saturation of the mathematical power, including overflow. -/
theorem checked_pow_default_spec (base : Std.U128) (exponent : Std.U32) :
    ∃ power, core.num.U128.checked_pow base exponent = ok power ∧
      (core.option.Option.unwrap_or power core.num.U128.MAX).val =
        min Std.U128.max (base.val ^ exponent.val) := by
  unfold core.num.U128.checked_pow
  by_cases hfit : base.val ^ exponent.val < U128.size
  · simp only [hfit, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    change (base.val ^ exponent.val) % 2 ^ 128 = min U128.max (base.val ^ exponent.val)
    have hbound : base.val ^ exponent.val < 2 ^ 128 := by simpa [U128.size, U128.numBits] using hfit
    rw [Nat.mod_eq_of_lt hbound, min_eq_right (by scalar_tac)]
  · simp only [hfit, ↓reduceIte]
    refine ⟨none, rfl, ?_⟩
    simp only [core.option.Option.unwrap_or]
    rw [min_eq_left (by scalar_tac)]
    simp [core.num.U128.MAX, U128.max, U128.numBits, U128.rMax]

/-- The intermediate product is a successful saturating multiplication. -/
theorem saturating_mul_spec (left right : Std.U128) :
    ∃ product, core.num.U128.saturating_mul left right = ok product ∧
      product.val = min Std.U128.max (left.val * right.val) := by
  refine ⟨_, rfl, ?_⟩
  simp only [UScalar.val, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle := min_le_left Std.U128.max (left.val * right.val)
  scalar_tac

private theorem usize_cast_u128_val (value : Std.Usize) :
    (UScalar.cast .U128 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U128_numBits_eq]
  cases System.Platform.numBits_eq <;> omega

private theorem u128_saturating_sub_one_val (value : Std.U128) :
    (core.num.U128.saturating_sub value 1#u128).val = value.val - 1 := by
  change (value.val - 1) % 2 ^ 128 = value.val - 1
  exact Nat.mod_eq_of_lt (by scalar_tac)

/-- The exact capacity formula, retaining both saturation limits. Capacity
    calculation succeeds whenever the packing-factor query succeeds, at every
    progressive depth and even for an arbitrary zero packing factor. -/
theorem ProgressiveTree.total_capacity_spec {T : Type}
    (ValueInst : Value T) (depth : Std.U32) {factor : Option Std.Usize}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor) :
    ∃ capacity, ProgressiveTree.total_capacity_at_depth ValueInst depth = ok capacity ∧
      capacity.val = min Std.Usize.max
        (((min Std.U128.max (4 ^ depth.val) - 1) / 3) *
          (core.option.Option.unwrap_or factor 1#usize).val) := by
  obtain ⟨power, hpower, hpowerVal⟩ := checked_pow_default_spec 4#u128 depth
  let reduced := core.num.U128.saturating_sub
    (core.option.Option.unwrap_or power core.num.U128.MAX) 1#u128
  have hreduced : reduced.val = min Std.U128.max (4 ^ depth.val) - 1 := by
    rw [u128_saturating_sub_one_val, hpowerVal]
    rfl
  have hdenominator : 4#u128 - 1#u128 = ok 3#u128 := by rfl
  obtain ⟨quotient, hquotient, hquotientVal⟩ :=
    UScalar.div_spec reduced (y := 3#u128) (by decide)
  obtain ⟨product, hproduct, hproductVal⟩ := saturating_mul_spec quotient
    (UScalar.cast .U128 (core.option.Option.unwrap_or factor 1#usize))
  obtain ⟨small, hsmall, hsmallEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_U128.spec product (UScalar.cast .U128 core.num.Usize.MAX))
  have hsmallVal : small.val = min Std.Usize.max
      (((min Std.U128.max (4 ^ depth.val) - 1) / 3) *
        (core.option.Option.unwrap_or factor 1#usize).val) := by
    have hmaxCast : (UScalar.cast .U128 core.num.Usize.MAX).val = Std.Usize.max := by
      rw [usize_cast_u128_val]
      simp
    rw [hsmallEq, core.cmp.impls.OrdU128.min_val, hproductVal, hmaxCast,
      usize_cast_u128_val, hquotientVal, hreduced]
    have hmaxBound : Std.Usize.max ≤ Std.U128.max := by scalar_tac
    rw [show (3#u128).val = 3 from rfl]
    omega
  have hsmallBound : small.val < 2 ^ UScalarTy.Usize.numBits := by
    have hle : small.val ≤ Std.Usize.max := by rw [hsmallVal]; exact min_le_left _ _
    scalar_tac
  refine ⟨UScalar.cast .Usize small, ?_, ?_⟩
  · dsimp only [reduced] at hquotient
    simp only [ProgressiveTree.total_capacity_at_depth, lift, bind_tc_ok,
      prog_tree_exponent_cast, hpower, hdenominator, hquotient, hfactor, hproduct, hsmall]
  · rw [UScalar.cast_val_mod_pow_of_inBounds_eq .Usize small hsmallBound, hsmallVal]

private theorem remove_u128_capacity_clip (power factor : Nat) :
    min Std.Usize.max (((min Std.U128.max power - 1) / 3) * factor) =
      min Std.Usize.max (((power - 1) / 3) * factor) := by
  by_cases hfit : power ≤ Std.U128.max
  · rw [min_eq_right hfit]
  · by_cases hz : factor = 0
    · simp [hz]
    · have hsmall : Std.Usize.max ≤ (Std.U128.max - 1) / 3 := by
        rcases Usize.bounds_eq with h | h <;>
          norm_num [h, U128.max, U128.numBits, U32.max, U32.numBits, U64.max, U64.numBits]
      have hfactor : 1 ≤ factor := by omega
      have hmul : (Std.U128.max - 1) / 3 ≤ ((Std.U128.max - 1) / 3) * factor := by
        simpa using Nat.mul_le_mul_left ((Std.U128.max - 1) / 3) hfactor
      have hdiv : (Std.U128.max - 1) / 3 ≤ (power - 1) / 3 := by omega
      have hmul' := Nat.mul_le_mul_right factor hdiv
      rw [min_eq_left (by omega : Std.U128.max ≤ power),
        min_eq_left (by omega), min_eq_left (by omega)]

/-- The internal `u128` saturation leaves the final machine-sized capacity
    equal to the clamped mathematical geometric sum. This formula holds even
    at depths where checked exponentiation overflows. -/
theorem ProgressiveTree.total_capacity_formula {T : Type}
    (ValueInst : Value T) (depth : Std.U32) {factor : Option Std.Usize}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor) :
    ∃ capacity, ProgressiveTree.total_capacity_at_depth ValueInst depth = ok capacity ∧
      capacity.val = min Std.Usize.max
        (((4 ^ depth.val - 1) / 3) * (core.option.Option.unwrap_or factor 1#usize).val) := by
  obtain ⟨capacity, hcapacity, hval⟩ := ProgressiveTree.total_capacity_spec ValueInst depth hfactor
  exact ⟨capacity, hcapacity, hval.trans (remove_u128_capacity_clip _ _)⟩

/-- Advancing one progressive layer adds precisely that layer's four-power
    number of leaf positions, before packing and machine-size clamping. -/
theorem progressive_sum_succ (depth : Nat) :
    (4 ^ (depth + 1) - 1) / 3 = (4 ^ depth - 1) / 3 + 4 ^ depth := by
  rw [pow_succ]
  have hpositive : 0 < 4 ^ depth := by positivity
  omega

private theorem remove_u128_product_clip (power factor : Nat) :
    min Std.Usize.max (min Std.U128.max power * factor) =
      min Std.Usize.max (power * factor) := by
  by_cases hfit : power ≤ Std.U128.max
  · rw [min_eq_right hfit]
  · by_cases hz : factor = 0
    · simp [hz]
    · have hbound : Std.Usize.max ≤ Std.U128.max := by
        rcases Usize.bounds_eq with h | h <;>
          norm_num [h, U128.max, U128.numBits, U32.max, U32.numBits, U64.max, U64.numBits]
      have hmul : Std.U128.max ≤ Std.U128.max * factor := by
        simpa using Nat.mul_le_mul_left Std.U128.max (show 1 ≤ factor by omega)
      have hmul' := Nat.mul_le_mul_right factor (show Std.U128.max ≤ power by omega)
      rw [min_eq_left (by omega : Std.U128.max ≤ power),
        min_eq_left (by omega), min_eq_left (by omega)]

/-- The cached capacity of the next layer is the clamped mathematical power,
    including internal exponentiation and multiplication saturation. -/
theorem ProgressiveTree.capacity_successor_formula {T : Type}
    (ValueInst : Value T) {depth next : Std.U32} {factor : Option Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor) :
    ∃ capacity, ProgressiveTree.capacity_at_depth ValueInst next = ok capacity ∧
      capacity.val = min Std.Usize.max
        (4 ^ depth.val * (core.option.Option.unwrap_or factor 1#usize).val) := by
  obtain ⟨power, hpower, hpowerVal⟩ := checked_pow_default_spec 4#u128 depth
  change (core.option.Option.unwrap_or power core.num.U128.MAX).val =
    min Std.U128.max (4 ^ depth.val) at hpowerVal
  obtain ⟨product, hproduct, hproductVal⟩ := saturating_mul_spec
    (core.option.Option.unwrap_or power core.num.U128.MAX)
    (UScalar.cast .U128 (core.option.Option.unwrap_or factor 1#usize))
  obtain ⟨small, hsmall, hsmallEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_U128.spec product (UScalar.cast .U128 core.num.Usize.MAX))
  have hsmallVal : small.val = min Std.Usize.max
      (4 ^ depth.val * (core.option.Option.unwrap_or factor 1#usize).val) := by
    have hmaxCast : (UScalar.cast .U128 core.num.Usize.MAX).val = Std.Usize.max := by
      rw [usize_cast_u128_val]
      simp
    rw [hsmallEq, core.cmp.impls.OrdU128.min_val, hproductVal, hmaxCast,
      usize_cast_u128_val, hpowerVal]
    have hmaxBound : Std.Usize.max ≤ Std.U128.max := by scalar_tac
    have hclip := remove_u128_product_clip (4 ^ depth.val)
      (core.option.Option.unwrap_or factor 1#usize).val
    omega
  have hsmallBound : small.val < 2 ^ UScalarTy.Usize.numBits := by
    have hle : small.val ≤ Std.Usize.max := by rw [hsmallVal]; exact min_le_left _ _
    scalar_tac
  refine ⟨UScalar.cast .Usize small, ?_, ?_⟩
  · simp only [ProgressiveTree.capacity_at_depth, checked_sub_of_successor hnext,
      lift, bind_tc_ok, prog_tree_exponent_cast, hpower, hfactor, hproduct, hsmall]
  · rw [UScalar.cast_val_mod_pow_of_inBounds_eq .Usize small hsmallBound, hsmallVal]

end milhouse.progressive_tree
