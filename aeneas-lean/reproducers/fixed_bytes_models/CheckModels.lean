import Tree.FunsExternal
import FixedSource.Funs

open Aeneas Aeneas.Std Result

/-- The extracted derived clone preserves the complete byte array. -/
theorem fixed_clone_agrees {N : Std.Usize} (value : Array Std.U8 N) :
    FixedSource.alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCloneClone.clone value =
      alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCloneClone.clone value := rfl

/-- The extracted constant and the local Result-valued zero constructor
produce the same array, including at length zero. -/
theorem fixed_zero_agrees (N : Std.Usize) :
    ok (FixedSource.alloy_primitives.bits.fixed.FixedBytes.ZERO N) =
      alloy_primitives.bits.fixed.FixedBytes.ZERO N := by
  unfold FixedSource.alloy_primitives.bits.fixed.FixedBytes.ZERO
    alloy_primitives.bits.fixed.FixedBytes.ZERO
  rfl

/-- Default delegates to the actual zero constant. -/
theorem fixed_default_agrees (N : Std.Usize) :
    FixedSource.alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault.default N =
      alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault.default N := by
  unfold FixedSource.alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault.default
    FixedSource.alloy_primitives.bits.fixed.FixedBytes.ZERO
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault.default
  rfl

/-- Derived equality agrees with list equality on every byte, using the
existing Aeneas array/byte comparison foundation. -/
theorem fixed_eq_agrees {N : Std.Usize} (left right : Array Std.U8 N) :
    FixedSource.alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq left right =
      alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq left right := by
  obtain ⟨answer, hrun, hanswer⟩ := WP.spec_imp_exists
    (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8
      left.to_slice right.to_slice (by
        intro x y
        simp [liftFun2, WP.spec_ok]))
  have harray : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      left right = ok answer := by
    simpa only [core.array.equality.PartialEqArray.eq,
      core.slice.cmp.PartialEqSlice.eq, Array.length_to_slice,
      Array.val_to_slice, Array.length_eq, Array.length] using hrun
  change core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      left right = ok (decide (left.val = right.val))
  rw [harray]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa only [Slice.eq_iff, Array.val_to_slice, decide_eq_true_eq] using hanswer

/-- Comparison with the actual zero constant agrees with checking all
bytes for zero. Array length is supplied by the type, not an extra premise. -/
theorem fixed_is_zero_agrees {N : Std.Usize} (value : Array Std.U8 N) :
    FixedSource.alloy_primitives.bits.fixed.FixedBytes.is_zero value =
      alloy_primitives.bits.fixed.FixedBytes.is_zero value := by
  rw [FixedSource.alloy_primitives.bits.fixed.FixedBytes.is_zero, fixed_eq_agrees]
  simp only [alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
    alloy_primitives.bits.fixed.FixedBytes.is_zero,
    FixedSource.alloy_primitives.bits.fixed.FixedBytes.ZERO, Array.repeat]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [List.eq_replicate_iff, value.property]

#print axioms fixed_clone_agrees
#print axioms fixed_zero_agrees
#print axioms fixed_default_agrees
#print axioms fixed_eq_agrees
#print axioms fixed_is_zero_agrees
