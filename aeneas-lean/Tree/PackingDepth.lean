import Tree.Nat.NextPowerOfTwo
import Tree.TrailingZeros

open Aeneas Aeneas.Std Result

namespace milhouse.utils

/-- The represented factor itself witnesses that its power fits in a word.
The overflow fallback and its `size_of` contract are not needed. -/
theorem int_log_power {factor depth : Std.Usize}
    (hpower : factor.val = 2 ^ depth.val) : int_log factor = ok depth := by
  have hnext : core.num.Usize.checked_next_power_of_two factor = ok (some factor) := by
    unfold core.num.Usize.checked_next_power_of_two
    rw [hpower, Nat.nextPowerOfTwo_two_pow, ← hpower]
    have hfit : factor.val < Usize.size := by scalar_tac
    rw [if_pos hfit]
    congr 1
    congr 1
    apply UScalar.eq_of_val_eq
    change (BitVec.ofNat System.Platform.numBits factor.val).toNat = factor.val
    rw [Usize.BitVec_ofNat_val]
    rfl
  let zeros : Std.U32 := ⟨BitVec.ofNat 32 (TreeAux.bvTrailingZeros factor.bv)⟩
  have hzeros : core.num.Usize.trailing_zeros factor = ok zeros := rfl
  have hpositive : 0 < factor.val := by rw [hpower]; positivity
  have hzerosVal : zeros.val = depth.val := by
    have h := milhouse.tree.usize_trailing_zeros_padic hpositive hzeros
    simpa only [hpower, padicValNat.prime_pow] using h
  have hcast : UScalar.cast .Usize zeros = depth := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq, hzerosVal]
    exact Nat.mod_eq_of_lt depth.hBounds
  simp only [int_log, hnext, bind_tc_ok, hzeros, hcast]

/-- Unpacked metadata skips the logarithm and supplies no packing depth. -/
theorem opt_packing_depth_of_none {T : Type} (hashInst : tree_hash.TreeHash T)
    (hfactor : opt_packing_factor hashInst = ok none) :
    opt_packing_depth hashInst = ok none := by
  simp [opt_packing_depth, hfactor,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

/-- The actual packing-depth computation follows from the factor query and
its power-of-two law, with no separate depth or termination assumption. -/
theorem opt_packing_depth_of_power {T : Type} (hashInst : tree_hash.TreeHash T)
    {factor depth : Std.Usize}
    (hfactor : opt_packing_factor hashInst = ok (some factor))
    (hpower : factor.val = 2 ^ depth.val) :
    opt_packing_depth hashInst = ok (some depth) := by
  simp [opt_packing_depth, hfactor,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch, int_log_power hpower]

end milhouse.utils
