import Tree.Ssz.VariableStep

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

private theorem variable_table_position (bytes tableTail : Slice Std.U8)
    (index : Std.Usize) (htable : 4 * index.val ≤ bytes.length)
    (htail : tableTail.val = bytes.val.drop (4 * index.val)) :
    ∃ position, index * 4#usize = ok position ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
        bytes { start := position } = ok tableTail := by
  have hmulBound : index.val * (4#usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hb := bytes.property
    change bytes.val.length ≤ Std.Usize.max at hb
    change index.val * 4 ≤ Std.Usize.max
    simp only [Slice.length] at htable
    omega
  obtain ⟨position, hmul, hpval⟩ := WP.spec_imp_exists (UScalar.mul_spec hmulBound)
  have hposition : position.val = 4 * index.val := by simpa [Nat.mul_comm] using hpval
  refine ⟨position, hmul, ?_⟩
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, hposition, htable, ↓reduceIte]
  congr 1
  apply Slice.ext
  simpa only [Slice.drop, Slice.from_val, hposition] using htail.symm

/-- A final offset beyond the input returns the exact byte-bounds error and
leaves the payload offset unchanged. -/
theorem SszItems.variable_item_last_out_of_bounds (bytes : Slice Std.U8)
    (first count offset : Std.Usize) (hbound : bytes.length < offset.val) :
    SszItems.variable_item bytes first count count offset =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OutOfBoundsByte offset), offset) := by
  have hnot : ¬ offset.val ≤ bytes.length := by omega
  simp only [SszItems.variable_item, ↓reduceIte, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeFromUsizeSlice.get, hnot, ↓reduceIte,
    bind_tc_ok, core.option.Option.ok_or]

/-- A malformed next table entry propagates its read error without changing
the payload offset or consulting the element decoder. -/
theorem SszItems.variable_item_read_error (bytes tableTail : Slice Std.U8)
    (first count index offset : Std.Usize) (error : ssz.decode.DecodeError)
    (hindex : index ≠ count) (htable : 4 * index.val ≤ bytes.length)
    (htail : tableTail.val = bytes.val.drop (4 * index.val))
    (hread : _root_.ssz.decode.read_offset tableTail = ok (core.result.Result.Err error)) :
    SszItems.variable_item bytes first count index offset =
      ok (core.result.Result.Err error, offset) := by
  obtain ⟨position, hmul, hslice⟩ := variable_table_position bytes tableTail index htable htail
  simp only [SszItems.variable_item, hindex, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET,
    bind_tc_ok, hmul, hslice, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- The fixed-section check precedes bounds and decreasing-offset checks. -/
theorem SszItems.variable_item_into_fixed (bytes tableTail : Slice Std.U8)
    (first count index offset nextOffset : Std.Usize)
    (hindex : index ≠ count) (htable : 4 * index.val ≤ bytes.length)
    (htail : tableTail.val = bytes.val.drop (4 * index.val))
    (hread : _root_.ssz.decode.read_offset tableTail = ok (core.result.Result.Ok nextOffset))
    (hfixed : nextOffset.val < first.val) :
    SszItems.variable_item bytes first count index offset =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetIntoFixedPortion nextOffset),
        offset) := by
  obtain ⟨position, hmul, hslice⟩ := variable_table_position bytes tableTail index htable htail
  have hlt : nextOffset < first := hfixed
  simp only [SszItems.variable_item, hindex, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET,
    bind_tc_ok, hmul, hslice, hread, core.result.Result.Insts.CoreOpsTry.branch, hlt, ↓reduceIte]

/-- The input-bounds check precedes decreasing offsets; rejection leaves the
current payload offset unchanged. -/
theorem SszItems.variable_item_out_of_bounds (bytes tableTail : Slice Std.U8)
    (first count index offset nextOffset : Std.Usize)
    (hindex : index ≠ count) (htable : 4 * index.val ≤ bytes.length)
    (htail : tableTail.val = bytes.val.drop (4 * index.val))
    (hread : _root_.ssz.decode.read_offset tableTail = ok (core.result.Result.Ok nextOffset))
    (hfixed : first.val ≤ nextOffset.val) (hbound : bytes.length < nextOffset.val) :
    SszItems.variable_item bytes first count index offset =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetOutOfBounds nextOffset),
        offset) := by
  obtain ⟨position, hmul, hslice⟩ := variable_table_position bytes tableTail index htable htail
  have hlt : ¬ nextOffset < first := not_lt.mpr hfixed
  have hgt : nextOffset > bytes.len := hbound
  simp only [SszItems.variable_item, hindex, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET,
    bind_tc_ok, hmul, hslice, hread, core.result.Result.Insts.CoreOpsTry.branch,
    hlt, hgt, ↓reduceIte]

/-- After fixed-section and input bounds pass, a backwards offset is rejected
with the offending next offset, retaining the current payload offset. -/
theorem SszItems.variable_item_decreasing (bytes tableTail : Slice Std.U8)
    (first count index offset nextOffset : Std.Usize)
    (hindex : index ≠ count) (htable : 4 * index.val ≤ bytes.length)
    (htail : tableTail.val = bytes.val.drop (4 * index.val))
    (hread : _root_.ssz.decode.read_offset tableTail = ok (core.result.Result.Ok nextOffset))
    (hfixed : first.val ≤ nextOffset.val) (hbound : nextOffset.val ≤ bytes.length)
    (horder : nextOffset.val < offset.val) :
    SszItems.variable_item bytes first count index offset =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetsAreDecreasing nextOffset),
        offset) := by
  obtain ⟨position, hmul, hslice⟩ := variable_table_position bytes tableTail index htable htail
  have hlt : ¬ nextOffset < first := not_lt.mpr hfixed
  have hgt : ¬ nextOffset > bytes.len := not_lt.mpr hbound
  have hback : offset > nextOffset := horder
  simp only [SszItems.variable_item, hindex, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET,
    bind_tc_ok, hmul, hslice, hread, core.result.Result.Insts.CoreOpsTry.branch,
    hlt, hgt, hback, ↓reduceIte]

end milhouse.ssz_items
