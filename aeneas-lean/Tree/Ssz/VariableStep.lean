import Tree.Ssz.VariableInit

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

theorem SszItems.next_variable_exhausted (bytes : Slice Std.U8)
    (first count index offset : Std.Usize) (hindex : count.val < index.val) :
    SszItems.next (.Variable bytes first count index offset) =
      ok (none, .Variable bytes first count index offset) := by
  have hgt : index > count := hindex
  simp only [SszItems.next, hgt, ↓reduceIte]

/-- The final item consumes the entire remaining payload, including an empty
payload when the last offset equals the input length. -/
theorem SszItems.variable_item_last (bytes : Slice Std.U8)
    (first count offset : Std.Usize) (hbound : offset.val ≤ bytes.length) :
    SszItems.variable_item bytes first count count offset =
      ok (core.result.Result.Ok (bytes.drop offset), offset) := by
  simp only [SszItems.variable_item, ↓reduceIte, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeFromUsizeSlice.get, hbound, ↓reduceIte,
    bind_tc_ok, core.option.Option.ok_or]

/-- A nonfinal item is exactly the range between its current offset and the
next table entry. The next offset may equal the current one. -/
theorem SszItems.variable_item_between (bytes part tableTail : Slice Std.U8)
    (first count index offset nextOffset : Std.Usize)
    (hindex : index ≠ count) (htable : 4 * index.val ≤ bytes.length)
    (htail : tableTail.val = bytes.val.drop (4 * index.val))
    (hread : _root_.ssz.decode.read_offset tableTail =
      ok (core.result.Result.Ok nextOffset))
    (hfixed : first.val ≤ nextOffset.val) (hbound : nextOffset.val ≤ bytes.length)
    (horder : offset.val ≤ nextOffset.val)
    (hpart : part.val = bytes.val.slice offset.val nextOffset.val) :
    SszItems.variable_item bytes first count index offset =
      ok (core.result.Result.Ok part, nextOffset) := by
  have hmulBound : index.val * (4#usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hb := bytes.property
    change bytes.val.length ≤ Std.Usize.max at hb
    change index.val * 4 ≤ Std.Usize.max
    simp only [Slice.length] at htable
    omega
  obtain ⟨position, hmul, hpval⟩ := WP.spec_imp_exists (UScalar.mul_spec hmulBound)
  have hposition : position.val = 4 * index.val := by simpa [Nat.mul_comm] using hpval
  have hslice : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := position } =
      ok tableTail := by
    simp only [core.slice.index.Slice.index,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index, hposition, htable, ↓reduceIte]
    congr 1
    apply Subtype.ext
    simpa only [Slice.drop, hposition] using htail.symm
  have hfirst : ¬ nextOffset < first := by exact not_lt.mpr hfixed
  have hlength : ¬ nextOffset > bytes.len := by exact not_lt.mpr hbound
  have hnext : ¬ offset > nextOffset := by exact not_lt.mpr horder
  have hget : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      bytes { start := offset, «end» := nextOffset } = ok (some part) := by
    simp only [core.slice.Slice.get,
      core.slice.index.SliceIndexRangeUsizeSlice.get, UScalar.le_equiv,
      horder, hbound, and_self, ↓reduceIte]
    congr 2
    exact Subtype.ext hpart.symm
  simp only [SszItems.variable_item, hindex, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET,
    bind_tc_ok, hmul, hslice, hread, core.result.Result.Insts.CoreOpsTry.branch,
    hfirst, hlength, hnext, ↓reduceIte, hget, core.option.Option.ok_or]

/-- A live cursor advances its index once and preserves the item helper's
exact result and next payload offset. The successor's type supplies its bound. -/
theorem SszItems.next_variable_step (bytes : Slice Std.U8)
    (first count index successor offset nextOffset : Std.Usize)
    (item : core.result.Result (Slice Std.U8) ssz.decode.DecodeError)
    (hindex : index.val ≤ count.val) (hsuccessor : successor.val = index.val + 1)
    (hitem : SszItems.variable_item bytes first count index offset = ok (item, nextOffset)) :
    SszItems.next (.Variable bytes first count index offset) =
      ok (some item, .Variable bytes first count successor nextOffset) := by
  have hbound : index.val + (1#usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    change index.val + 1 ≤ Std.Usize.max
    rw [← hsuccessor]
    scalar_tac
  obtain ⟨result, hadd, hrval⟩ := WP.spec_imp_exists (UScalar.add_spec hbound)
  have heq : result = successor := by
    apply UScalar.eq_of_val_eq
    change result.val = index.val + 1 at hrval
    omega
  subst result
  have hgt : ¬ index > count := not_lt.mpr hindex
  simp! only [SszItems.next, hgt, ↓reduceIte, hadd, hitem, bind_tc_ok]

end milhouse.ssz_items
