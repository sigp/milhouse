import Tree.ProgressiveTree
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

end milhouse.progressive_tree
