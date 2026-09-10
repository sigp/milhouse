import Tree.ProgressiveList.Decode.ErrorResult
import Tree.Ssz.VariableErrors

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem read_first_two_offsets (bytes : Slice Std.U8) (first second : Std.Usize)
    (rest : _root_.List Std.U8) (hfirstFit : first.val ≤ Std.U32.max)
    (hsecondFit : second.val ≤ Std.U32.max)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes first.val ++
      _root_.ssz.encode.offsetBytes second.val ++ rest) :
    _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok first) ∧
      _root_.ssz.decode.read_offset (bytes.drop 4#usize) = ok (core.result.Result.Ok second) := by
  refine ⟨_root_.ssz.decode.read_offset_offsetBytes bytes first
    (_root_.ssz.encode.offsetBytes second.val ++ rest) hfirstFit
    (by simpa only [_root_.List.append_assoc] using hbytes), ?_⟩
  apply _root_.ssz.decode.read_offset_offsetBytes (bytes.drop 4#usize) second rest hsecondFit
  simp only [Slice.drop, Slice.from_val]
  change bytes.val.drop 4 = _
  rw [hbytes, _root_.List.append_assoc, ← _root_.ssz.encode.offsetBytes_length first.val,
    _root_.List.drop_left]

/-- A second offset inside the fixed section is rejected before any element
decoder is called, even if the bytes that would form the first payload are
invalid. The theorem reads the actual first two little-endian offset words. -/
theorem ProgressiveList.from_ssz_bytes_second_offset_into_fixed {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (first count second : Std.Usize) (rest : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirstFit : first.val ≤ Std.U32.max)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes first.val ++
      _root_.ssz.encode.offsetBytes second.val ++ rest)
    (hfirst : first.val = 4 * count.val) (hcount : 1 < count.val)
    (hbound : first.val ≤ bytes.length) (hbad : second.val < first.val)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetIntoFixedPortion second)) := by
  obtain ⟨hreadFirst, hreadSecond⟩ := read_first_two_offsets bytes first second rest
    hfirstFit (by omega) hbytes
  have hindex : (1#usize) ≠ count := by
    intro h
    have hv := congrArg UScalar.val h
    change 1 = count.val at hv
    omega
  have hitem := ssz_items.SszItems.variable_item_into_fixed bytes (bytes.drop 4#usize)
    first count 1#usize first second hindex (by change 4 * 1 ≤ bytes.length; omega)
    (by simp [Slice.drop]) hreadSecond hbad
  apply ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count []
    (.OffsetIntoFixedPortion second) hvariable hreadFirst hfirst (by omega) hbound
    (ssz_items.SszItems.Decodes.boundary_error
      (ssz_items.SszItems.next_variable_step bytes first count 1#usize 2#usize first first
        (.Err (.OffsetIntoFixedPortion second)) (by change 1 ≤ count.val; omega) rfl hitem))
    hlayout updates hdefault

/-- An in-table second entry beyond the input is rejected before decoding the
first element. No element-codec law, later-offset law, or capacity assumption is
needed; the valid first offset supplies the builder's bounds. -/
theorem ProgressiveList.from_ssz_bytes_second_offset_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (first count second : Std.Usize) (rest : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirstFit : first.val ≤ Std.U32.max) (hsecondFit : second.val ≤ Std.U32.max)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes first.val ++
      _root_.ssz.encode.offsetBytes second.val ++ rest)
    (hfirst : first.val = 4 * count.val) (hcount : 1 < count.val)
    (hbound : first.val ≤ bytes.length) (hbad : bytes.length < second.val)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetOutOfBounds second)) := by
  obtain ⟨hreadFirst, hreadSecond⟩ := read_first_two_offsets bytes first second rest
    hfirstFit hsecondFit hbytes
  have hindex : (1#usize) ≠ count := by
    intro h
    have hv := congrArg UScalar.val h
    change 1 = count.val at hv
    omega
  have hitem := ssz_items.SszItems.variable_item_out_of_bounds bytes (bytes.drop 4#usize)
    first count 1#usize first second hindex (by change 4 * 1 ≤ bytes.length; omega)
    (by simp [Slice.drop]) hreadSecond (by omega) hbad
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count []
    (.OffsetOutOfBounds second) hvariable hreadFirst hfirst (by omega) hbound
    (ssz_items.SszItems.Decodes.boundary_error
      (ssz_items.SszItems.next_variable_step bytes first count 1#usize 2#usize first first
        (.Err (.OffsetOutOfBounds second)) (by change 1 ≤ count.val; omega) rfl hitem))
    hlayout updates hdefault

/-- A decreasing third offset is detected after decoding the first payload,
and before decoding the second. Only the first payload's successful decoder
call is required. Bounds for the first and third words follow from the second
word, and the valid table supplies all builder capacity bounds. -/
theorem ProgressiveList.from_ssz_bytes_third_offset_decreasing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes part : Slice Std.U8) (first count second third : Std.Usize)
    (rest : _root_.List Std.U8) (value : T)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hsecondFit : second.val ≤ Std.U32.max)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes first.val ++
      _root_.ssz.encode.offsetBytes second.val ++ _root_.ssz.encode.offsetBytes third.val ++ rest)
    (hfirst : first.val = 4 * count.val) (hcount : 2 < count.val)
    (horder : first.val ≤ second.val) (hbound : second.val ≤ bytes.length)
    (hfixed : first.val ≤ third.val) (hdecreasing : third.val < second.val)
    (hpart : part.val = bytes.val.slice first.val second.val)
    (hdecode : ValueInst.sszdecodeDecodeInst.from_ssz_bytes part = ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetsAreDecreasing third)) := by
  obtain ⟨hreadFirst, hreadSecond⟩ := read_first_two_offsets bytes first second
    (_root_.ssz.encode.offsetBytes third.val ++ rest) (by omega) hsecondFit
    (by simpa only [_root_.List.append_assoc] using hbytes)
  have hreadThird : _root_.ssz.decode.read_offset (bytes.drop 8#usize) =
      ok (core.result.Result.Ok third) := by
    apply _root_.ssz.decode.read_offset_offsetBytes (bytes.drop 8#usize) third rest (by omega)
    have hlen : (_root_.ssz.encode.offsetBytes first.val ++
        _root_.ssz.encode.offsetBytes second.val).length = 8 := by
      simp only [_root_.List.length_append, _root_.ssz.encode.offsetBytes_length]
    have hcanonical : bytes.val = (_root_.ssz.encode.offsetBytes first.val ++
        _root_.ssz.encode.offsetBytes second.val) ++
        (_root_.ssz.encode.offsetBytes third.val ++ rest) := by
      simpa only [_root_.List.append_assoc] using hbytes
    simp only [Slice.drop, Slice.from_val]
    change bytes.val.drop 8 = _
    rw [hcanonical, ← hlen, _root_.List.drop_left]
  have hindexOne : (1#usize) ≠ count := by
    intro h
    have hv := congrArg UScalar.val h
    change 1 = count.val at hv
    omega
  have hindexTwo : (2#usize) ≠ count := by
    intro h
    have hv := congrArg UScalar.val h
    change 2 = count.val at hv
    omega
  have hfirstItem := ssz_items.SszItems.variable_item_between bytes part (bytes.drop 4#usize)
    first count 1#usize first second hindexOne (by change 4 * 1 ≤ bytes.length; omega)
    (by simp [Slice.drop]) hreadSecond horder hbound horder hpart
  have hsecondItem := ssz_items.SszItems.variable_item_decreasing bytes (bytes.drop 8#usize)
    first count 2#usize second third hindexTwo (by change 4 * 2 ≤ bytes.length; omega)
    (by simp [Slice.drop]) hreadThird hfixed (by omega) hdecreasing
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count [value]
    (.OffsetsAreDecreasing third) hvariable hreadFirst hfirst (by omega) (by omega)
    (ssz_items.SszItems.Decodes.cons
      (ssz_items.SszItems.next_variable_step bytes first count 1#usize 2#usize first second
        (.Ok part) (by change 1 ≤ count.val; omega) rfl hfirstItem) hdecode
      (ssz_items.SszItems.Decodes.boundary_error
        (ssz_items.SszItems.next_variable_step bytes first count 2#usize 3#usize second second
          (.Err (.OffsetsAreDecreasing third)) (by change 2 ≤ count.val; omega) rfl hsecondItem)))
    hlayout updates hdefault

end milhouse.progressive_list
