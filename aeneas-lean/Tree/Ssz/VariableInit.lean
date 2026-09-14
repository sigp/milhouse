import Tree.Ssz.ReadOffset
import Tree.Ssz.DecodedItems

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

/-- The first offset's bounds check precedes its alignment check. -/
theorem SszItems.variable_out_of_bounds (bytes : Slice Std.U8) (first : Std.Usize)
    (hread : _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok first))
    (hbound : bytes.length < first.val) :
    SszItems.variable bytes = ok (core.result.Result.Err
      (ssz.decode.DecodeError.OffsetOutOfBounds first)) := by
  have hgt : first > bytes.len := by simpa only [UScalar.lt_equiv, Slice.len_val]
  simp only [SszItems.variable, hread, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok, hgt, ↓reduceIte]

/-- A misaligned fixed section is rejected before creating a cursor. -/
theorem SszItems.variable_unaligned (bytes : Slice Std.U8) (first : Std.Usize)
    (hread : _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok first))
    (hbound : first.val ≤ bytes.length) (halign : first.val % 4 ≠ 0) :
    SszItems.variable bytes = ok (core.result.Result.Err
      (ssz.decode.DecodeError.InvalidListFixedBytesLen first)) := by
  obtain ⟨remainder, hrem, hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec first (y := 4#usize) (by simp))
  have hrne : remainder ≠ 0#usize := by
    intro h
    subst remainder
    change 0 = first.val % 4 at hrval
    omega
  have hgt : ¬ first > bytes.len := by
    simpa only [UScalar.lt_equiv, Slice.len_val, not_lt]
  simp only [SszItems.variable, hread, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok, hgt, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET, hrem,
    bne_iff_ne]
  rw [if_pos hrne]

/-- A zero first offset cannot describe a nonempty variable item table. -/
theorem SszItems.variable_zero (bytes : Slice Std.U8)
    (hread : _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok 0#usize)) :
    SszItems.variable bytes = ok (core.result.Result.Err
      (ssz.decode.DecodeError.InvalidListFixedBytesLen 0#usize)) := by
  have hgt : ¬ (0#usize) > bytes.len := by scalar_tac
  obtain ⟨remainder, hrem, hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (0#usize) (y := 4#usize) (by simp))
  have hrzero : remainder = 0#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hrval
  subst remainder
  simp only [SszItems.variable, hread, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok, hgt, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET, hrem]
  rfl

/-- A positive, complete four-byte offset table initializes its exact item
count and first payload boundary. No element decoder is called here. -/
theorem SszItems.variable_valid (bytes : Slice Std.U8) (first count : Std.Usize)
    (hread : _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok first))
    (hfirst : first.val = 4 * count.val) (hcount : 0 < count.val)
    (hbound : first.val ≤ bytes.length) :
    SszItems.variable bytes = ok (core.result.Result.Ok
      (.Variable bytes first count 1#usize first)) := by
  obtain ⟨remainder, hrem, hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec first (y := 4#usize) (by simp))
  have hrzero : remainder = 0#usize := by
    apply UScalar.eq_of_val_eq
    simpa [hfirst] using hrval
  subst remainder
  obtain ⟨quotient, hdiv, hqval⟩ := UScalar.div_spec first (y := 4#usize) (by simp)
  have hq : quotient = count := by
    apply UScalar.eq_of_val_eq
    simpa [hfirst] using hqval
  subst quotient
  have hgt : ¬ first > bytes.len := by
    simpa only [UScalar.lt_equiv, Slice.len_val, not_lt]
  have hlt : ¬ first < 4#usize := by
    change ¬ first.val < 4
    omega
  simp only [SszItems.variable, hread, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok, hgt, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET, hrem,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hlt, hdiv]

end milhouse.ssz_items
