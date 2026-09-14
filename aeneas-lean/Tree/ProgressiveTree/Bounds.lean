import Tree.ProgressiveTree.Density

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Every materialized spine layer has a representable binary capacity. The
    terminal zero needs no bound because lookup returns before doing arithmetic. -/
def ProgressiveTree.Fits {T : Type} (factor : Option Std.Usize) :
    ProgressiveTree T → Nat → Prop
  | .ProgressiveZero, _ => True
  | .ProgressiveNode _ _ right, depth =>
    subtreeCapacity factor (2 * depth) < 2 ^ System.Platform.numBits ∧
      right.Fits factor (depth + 1)

theorem subtreeCapacity_mono_depth (factor : Option Std.Usize) {left right : Nat}
    (hle : left ≤ right) : subtreeCapacity factor left ≤ subtreeCapacity factor right := by
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hle)

/-- A representable progressive layer supplies successful depth advancement,
    binary-depth conversion, and the complete binary routing bound. -/
theorem next_layer_bounds {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) (depth : Std.U32)
    (hfit : subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits) :
    ∃ next binary, depth + 1#u32 = ok next ∧
      ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary ∧
      binary.val = 2 * depth.val ∧ binary.val + packingDepth.val < System.Platform.numBits := by
  have hbits : packingDepth.val + 2 * depth.val < System.Platform.numBits := by
    rw [hlayout.subtreeCapacity_eq_two_pow] at hfit
    by_contra hnot
    have hle : System.Platform.numBits ≤ packingDepth.val + 2 * depth.val := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega
  have hplatform : System.Platform.numBits ≤ 64 := by cases System.Platform.numBits_eq <;> omega
  have hdepthBound : depth.val + 1 ≤ Std.U32.max := by
    norm_num [U32.max, U32.numBits]
    omega
  obtain ⟨next, hnext, hnextVal⟩ := Aeneas.Std.WP.spec_imp_exists
    (U32.add_spec (x := depth) (y := 1#u32) (by simpa using hdepthBound))
  have hcast : (UScalar.cast .Usize depth).val = depth.val := by
    apply UScalar.cast_val_mod_pow_greater_numBits_eq
    simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
    cases System.Platform.numBits_eq <;> omega
  have hmachine : 64 ≤ Std.Usize.max := by
    rcases Usize.bounds_eq with h | h <;>
      norm_num [h, U32.max, U32.numBits, U64.max, U64.numBits]
  obtain ⟨binary, hbinary, hbinaryVal⟩ := Aeneas.Std.WP.spec_imp_exists
    (Usize.mul_spec (x := 2#usize) (y := UScalar.cast .Usize depth) (by simp [hcast]; omega))
  refine ⟨next, binary, hnext, ?_, ?_, ?_⟩
  · rw [ProgressiveTree.binary_depth_successor_eq ValueInst hnext]
    exact hbinary
  · simpa [hcast] using hbinaryVal
  · simp [hcast] at hbinaryVal
    omega

end milhouse.progressive_tree
