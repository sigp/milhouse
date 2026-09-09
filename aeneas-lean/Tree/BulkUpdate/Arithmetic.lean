import Tree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Every checked operation used to split a binary bulk-update window
succeeds when its aligned global endpoint fits. The returned child ranges
partition exactly that window, including a nonzero global offset. -/
theorem Tree.bulk_update_node_arithmetic {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (depth prefix1 offset : Std.Usize) (hpositive : 0 < depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max) :
    ∃ nd shift stride parentShift width subtreeEnd lo middle stop,
      depth - 1#usize = ok nd ∧ nd.val + 1 = depth.val ∧
      nd + packingDepth = ok shift ∧ 1#usize <<< shift = ok stride ∧
      depth + packingDepth = ok parentShift ∧ 1#usize <<< parentShift = ok width ∧
      prefix1 + width = ok subtreeEnd ∧ prefix1 + offset = ok lo ∧
      (prefix1 ||| stride) + offset = ok middle ∧ subtreeEnd + offset = ok stop ∧
      (prefix1 ||| stride).val = prefix1.val + subtreeCapacity factor nd.val ∧
      lo.val = prefix1.val + offset.val ∧
      middle.val = prefix1.val + offset.val + subtreeCapacity factor nd.val ∧
      stop.val = prefix1.val + offset.val + subtreeCapacity factor depth.val := by
  have hmax : Std.Usize.max < 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all [Std.Usize.max, Std.Usize.numBits]
  have hpower : 2 ^ (depth.val + packingDepth.val) ≤ Std.Usize.max := by
    rw [Nat.add_comm, ← hlayout.subtreeCapacity_eq_two_pow]
    omega
  have hbits : depth.val + packingDepth.val < System.Platform.numBits := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt h)
    omega
  have hbitsBound : System.Platform.numBits < 2 ^ System.Platform.numBits := Nat.lt_two_pow_self
  obtain ⟨nd, hnd, hndVal⟩ := usize_sub_one_succeeds hpositive
  obtain ⟨shift, hshift, hshiftVal⟩ := usize_add_succeeds (x := nd) (y := packingDepth) (by omega)
  obtain ⟨parentShift, hparentShift, hparentShiftVal⟩ :=
    usize_add_succeeds (x := depth) (y := packingDepth) (by omega)
  have hshiftBits : shift.val < UScalarTy.Usize.numBits := by
    simpa only [UScalarTy.Usize_numBits_eq] using (show shift.val < System.Platform.numBits by omega)
  have hparentBits : parentShift.val < UScalarTy.Usize.numBits := by
    simpa only [UScalarTy.Usize_numBits_eq] using
      (show parentShift.val < System.Platform.numBits by omega)
  obtain ⟨stride, hstride, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec 1#usize shift (UScalar.size .Usize) hshiftBits rfl)
  obtain ⟨width, hwidth, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec 1#usize parentShift (UScalar.size .Usize) hparentBits rfl)
  have hstrideVal : stride.val = subtreeCapacity factor nd.val := by
    rw [usize_shift_left_one_val hstride, hlayout.subtreeCapacity_eq_two_pow]
    congr 1
    omega
  have hwidthVal : width.val = subtreeCapacity factor depth.val := by
    rw [usize_shift_left_one_val hwidth, hlayout.subtreeCapacity_eq_two_pow]
    congr 1
    omega
  have hright : (prefix1 ||| stride).val = prefix1.val + subtreeCapacity factor nd.val := by
    rw [usize_or_val, usize_shift_left_one_val hstride]
    have hparent : subtreeCapacity factor depth.val = 2 ^ (shift.val + 1) := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    rw [or_two_pow_aligned (by rwa [← hparent])]
    rw [← usize_shift_left_one_val hstride, hstrideVal]
  have hcap : subtreeCapacity factor depth.val = 2 * subtreeCapacity factor nd.val := by
    rw [hndVal]
    simp only [subtreeCapacity, pow_succ]
    ring
  obtain ⟨subtreeEnd, hsubtreeEnd, hsubtreeEndVal⟩ :=
    usize_add_succeeds (x := prefix1) (y := width) (by omega)
  obtain ⟨lo, hlo, hloVal⟩ := usize_add_succeeds (x := prefix1) (y := offset) (by omega)
  obtain ⟨middle, hmiddle, hmiddleVal⟩ :=
    usize_add_succeeds (x := prefix1 ||| stride) (y := offset) (by omega)
  obtain ⟨stop, hstop, hstopVal⟩ := usize_add_succeeds (x := subtreeEnd) (y := offset) (by omega)
  exact ⟨nd, shift, stride, parentShift, width, subtreeEnd, lo, middle, stop,
    hnd, by omega, hshift, hstride, hparentShift, hwidth, hsubtreeEnd, hlo, hmiddle, hstop,
    hright, hloVal, by omega, by omega⟩

end milhouse.tree
