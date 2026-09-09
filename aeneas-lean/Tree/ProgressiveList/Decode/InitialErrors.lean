import Tree.ProgressiveList.Decode.Entry
import Tree.Ssz.VariableInit

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem offset_input_nonempty (bytes : Slice Std.U8) (offset : Nat)
    (rest : _root_.List Std.U8)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes offset ++ rest) : bytes.val ≠ [] := by
  intro hempty
  have h := congrArg _root_.List.length hbytes
  simp only [hempty, _root_.List.length_nil, _root_.List.length_append,
    _root_.ssz.encode.offsetBytes_length] at h
  omega

private theorem from_ssz_bytes_initial_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (hnonempty : bytes.val ≠ [])
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (error : ssz.decode.DecodeError)
    (hinit : ssz_items.SszItems.variable bytes = ok (core.result.Result.Err error)) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  simp [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
    hnonempty, hvariable, hinit,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- A first offset beyond the input is rejected before checking alignment.
This public result depends only on the actual bytes and variable-format
metadata, without packing, map, element-decoding, or construction laws. -/
theorem ProgressiveList.from_ssz_bytes_first_offset_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (first : Std.Usize) (rest : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfit : first.val ≤ Std.U32.max)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes first.val ++ rest)
    (hbound : bytes.length < first.val) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.OffsetOutOfBounds first)) := by
  exact from_ssz_bytes_initial_error ValueInst mapInst bytes
    (offset_input_nonempty bytes first.val rest hbytes) hvariable _
    (ssz_items.SszItems.variable_out_of_bounds bytes first
      (_root_.ssz.decode.read_offset_offsetBytes bytes first rest hfit hbytes) hbound)

/-- An in-bounds but misaligned first offset returns the exact fixed-section
length error before building a list or decoding an element. -/
theorem ProgressiveList.from_ssz_bytes_first_offset_unaligned {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (first : Std.Usize) (rest : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfit : first.val ≤ Std.U32.max)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes first.val ++ rest)
    (hbound : first.val ≤ bytes.length) (halign : first.val % 4 ≠ 0) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.InvalidListFixedBytesLen first)) := by
  exact from_ssz_bytes_initial_error ValueInst mapInst bytes
    (offset_input_nonempty bytes first.val rest hbytes) hvariable _
    (ssz_items.SszItems.variable_unaligned bytes first
      (_root_.ssz.decode.read_offset_offsetBytes bytes first rest hfit hbytes) hbound halign)

/-- A zero first offset is invalid even with arbitrary following bytes.
Empty-input behavior is separate because this input contains four offset bytes. -/
theorem ProgressiveList.from_ssz_bytes_first_offset_zero {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (rest : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hbytes : bytes.val = _root_.ssz.encode.offsetBytes 0 ++ rest) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.InvalidListFixedBytesLen 0#usize)) := by
  exact from_ssz_bytes_initial_error ValueInst mapInst bytes
    (offset_input_nonempty bytes 0 rest hbytes) hvariable _
    (ssz_items.SszItems.variable_zero bytes
      (_root_.ssz.decode.read_offset_offsetBytes bytes 0#usize rest (by scalar_tac) hbytes))

end milhouse.progressive_list
