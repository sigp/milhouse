import Tree.ProgressiveTree

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem u32_cast_usize_val (value : Std.U32) :
    (UScalar.cast .Usize value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
  cases System.Platform.numBits_eq <;> omega

/-- Four-way progressive growth corresponds to two binary levels. -/
theorem prog_tree_binary_scale : PROG_TREE_BINARY_SCALE = ok 2#usize := by
  have hfour : (4#System.Platform.numBits) ≠ 0#System.Platform.numBits := by
    intro heq
    have hval := congrArg BitVec.toNat heq
    rcases System.Platform.numBits_eq with h | h <;> norm_num [h] at hval
  have hzeros : core.num.Usize.trailing_zeros PROG_TREE_EXPONENT = ok 2#u32 := by
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    unfold PROG_TREE_EXPONENT
    simp only [UScalar.val, UScalarTy.U32_numBits_eq, BitVec.toNat_ofNat]
    rcases System.Platform.numBits_eq with h | h <;>
      simp [TreeAux.bvTrailingZeros, TreeAux.natTrailingZeros, h] <;>
      split_ifs with hz
    all_goals first | exact False.elim (hfour hz) | rfl
  simp only [PROG_TREE_BINARY_SCALE, hzeros, bind_tc_ok]
  apply congrArg Result.ok
  apply UScalar.eq_of_val_eq
  rw [u32_cast_usize_val]
  simp

private theorem checked_sub_of_successor {depth next : Std.U32}
    (hnext : depth + 1#u32 = ok next) : U32.checked_sub next 1#u32 = some depth := by
  have hadd := UScalar.add_equiv depth 1#u32
  rw [hnext] at hadd
  simp at hadd
  obtain ⟨previous, hprevious, hval, _⟩ := Aeneas.Std.WP.spec_imp_exists
    (U32.sub_spec (x := next) (y := 1#u32) (by scalar_tac))
  have heq : previous = depth := by scalar_tac
  subst previous
  simp [U32.checked_sub, core.num.checked_sub_UScalar, hprevious, Option.ofResult]

theorem ProgressiveTree.binary_depth_zero {T : Type} (ValueInst : Value T) :
    ProgressiveTree.prog_depth_to_binary_depth ValueInst 0#u32 = ok 0#usize := by rfl

/-- The next layer has twice the current progressive depth in binary levels.
    The equality preserves the checked multiplication's overflow behavior. -/
theorem ProgressiveTree.binary_depth_successor_eq {T : Type} (ValueInst : Value T)
    {depth next : Std.U32} (hnext : depth + 1#u32 = ok next) :
    ProgressiveTree.prog_depth_to_binary_depth ValueInst next =
      2#usize * UScalar.cast .Usize depth := by
  simp only [ProgressiveTree.prog_depth_to_binary_depth, checked_sub_of_successor hnext,
    lift, bind_tc_ok, prog_tree_binary_scale]

/-- Successful binary-depth calculation supplies the multiplication bound;
    no additional machine-word bound is assumed. -/
theorem ProgressiveTree.binary_depth_successor_val {T : Type} (ValueInst : Value T)
    {depth next : Std.U32} {binary : Std.Usize} (hnext : depth + 1#u32 = ok next)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary) :
    binary.val = 2 * depth.val := by
  rw [ProgressiveTree.binary_depth_successor_eq ValueInst hnext] at hbinary
  have hmul := UScalar.mul_equiv 2#usize (UScalar.cast .Usize depth)
  change UScalar.mul _ _ = ok binary at hbinary
  rw [hbinary] at hmul
  simp at hmul
  exact hmul.2.1

end milhouse.progressive_tree
