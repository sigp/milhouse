import Tree.ProgressiveList.Decode.ErrorResult
import Tree.Ssz.VariableElementErrors

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- After any successful variable prefix, a nonfinal payload error is
returned unchanged once its boundary checks pass. Later offsets and payloads
are unconstrained; empty invalid payloads are supported. All parser, builder,
and capacity obligations are established internally. -/
theorem ProgressiveList.from_ssz_bytes_variable_element_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (encode : T → _root_.List Std.U8) (bytes part : Slice Std.U8)
    (first count current nextOffset : Std.Usize) (values : _root_.List T)
    (tableSuffix payloadSuffix : _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirst : first.val = 4 * count.val) (hcount : values.length + 1 < count.val)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hnextFit : nextOffset.val ≤ Std.U32.max) (hnextBound : nextOffset.val ≤ bytes.length)
    (horder : current.val ≤ nextOffset.val)
    (htable : bytes.val = _root_.ssz.encode.offsets encode first.val values ++
      _root_.ssz.encode.offsetBytes current.val ++ _root_.ssz.encode.offsetBytes nextOffset.val ++
        tableSuffix)
    (hpayload : bytes.val.drop first.val = values.flatMap encode ++ payloadSuffix)
    (hdecode : ∀ value ∈ values, ∀ bytes : Slice Std.U8,
      bytes.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes bytes =
        ok (core.result.Result.Ok value))
    (hpart : part.val = bytes.val.slice current.val nextOffset.val)
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes part = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  have hread := _root_.ssz.decode.read_offset_prefix encode bytes first current values
    (_root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix) hcurrent (by omega)
    (by simpa only [_root_.List.append_assoc] using htable)
  have hitems := ssz_items.SszItems.variable_decodes_element_error
    ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode bytes part first count current nextOffset
    values tableSuffix payloadSuffix error hfirst hcount hcurrent hnextFit hnextBound horder
    htable hpayload hdecode hpart herror
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count values error
    hvariable hread hfirst (by omega) (by omega) hitems hlayout updates hdefault

/-- The public variable decoder returns its final payload's element error
after any successful prefix. That final payload may be empty. Its boundary and
all builder bounds follow from the complete offset table and payload layout. -/
theorem ProgressiveList.from_ssz_bytes_variable_final_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (encode : T → _root_.List Std.U8) (bytes last : Slice Std.U8)
    (first count current : Std.Usize) (values : _root_.List T)
    (tableSuffix : _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirst : first.val = 4 * count.val) (hcount : values.length + 1 = count.val)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hfit : current.val ≤ Std.U32.max)
    (htable : bytes.val = _root_.ssz.encode.offsets encode first.val values ++
      _root_.ssz.encode.offsetBytes current.val ++ tableSuffix)
    (hpayload : bytes.val.drop first.val = values.flatMap encode ++ last.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes last = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  have hfirstBound : first.val ≤ bytes.length := by
    have hlen := congrArg _root_.List.length htable
    simp only [_root_.List.length_append, _root_.ssz.encode.offsets_length,
      _root_.ssz.encode.offsetBytes_length] at hlen
    simp only [Slice.length]
    omega
  have hread := _root_.ssz.decode.read_offset_prefix encode bytes first current values tableSuffix
    hcurrent hfit htable
  have hitems := ssz_items.SszItems.variable_decodes_final_error
    ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode bytes last first count current values
    tableSuffix error hfirst hcount hcurrent hfit htable hpayload hdecode herror
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count values error
    hvariable hread hfirst (by omega) hfirstBound hitems hlayout updates hdefault

end milhouse.progressive_list
