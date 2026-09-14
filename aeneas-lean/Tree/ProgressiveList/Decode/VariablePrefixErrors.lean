import Tree.ProgressiveList.Decode.ErrorResult
import Tree.Ssz.VariablePrefixErrors

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The public variable decoder returns the exact first malformed offset
after any successful prefix. Raw table and payload bytes determine every
cursor step; element laws apply only to preceding values. There are no list,
builder, parser-result, or additional sequence-capacity assumptions. -/
theorem ProgressiveList.from_ssz_bytes_variable_offset_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (encode : T → _root_.List Std.U8) (bytes : Slice Std.U8)
    (first count current nextOffset : Std.Usize) (values : _root_.List T)
    (tableSuffix payloadSuffix : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirst : first.val = 4 * count.val) (hcount : values.length + 1 < count.val)
    (hfirstBound : first.val ≤ bytes.length)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hcurrentFit : current.val ≤ Std.U32.max) (hnextFit : nextOffset.val ≤ Std.U32.max)
    (htable : bytes.val = _root_.ssz.encode.offsets encode first.val values ++
      _root_.ssz.encode.offsetBytes current.val ++ _root_.ssz.encode.offsetBytes nextOffset.val ++
        tableSuffix)
    (hpayload : bytes.val.drop first.val = values.flatMap encode ++ payloadSuffix)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    (hbad : nextOffset.val < first.val ∨ bytes.length < nextOffset.val ∨
      nextOffset.val < current.val)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    let error := if nextOffset.val < first.val then
        ssz.decode.DecodeError.OffsetIntoFixedPortion nextOffset
      else if bytes.length < nextOffset.val then ssz.decode.DecodeError.OffsetOutOfBounds nextOffset
      else ssz.decode.DecodeError.OffsetsAreDecreasing nextOffset
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  have hread := _root_.ssz.decode.read_offset_prefix encode bytes first current values
    (_root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix) hcurrent hcurrentFit
    (by simpa only [_root_.List.append_assoc] using htable)
  have hitems := ssz_items.SszItems.variable_decodes_offset_error
    ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode bytes first count current nextOffset values
    tableSuffix payloadSuffix hfirst hcount hfirstBound hcurrent hcurrentFit hnextFit
    htable hpayload hdecode hbad
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count values _
    hvariable hread hfirst (by omega) hfirstBound hitems hlayout updates hdefault

end milhouse.progressive_list
