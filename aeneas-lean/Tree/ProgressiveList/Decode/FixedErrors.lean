import Tree.ProgressiveList.Decode.ErrorResult
import Tree.Ssz.FixedPrefix

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The public fixed decoder returns the final chunk's element error after
successfully decoding its prefix. A short final chunk is passed through intact;
there is no earlier list-alignment error. Capacity is needed only for the
successful prefix, which is finalized before returning the decoding error. -/
theorem ProgressiveList.from_ssz_bytes_fixed_final_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes last : Slice Std.U8) (width : Std.Usize) (values : _root_.List T)
    (encode : T → _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode ++ last.val)
    (hvalueWidth : ∀ value ∈ values, (encode value).length = width.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    (hlast : last.val ≠ []) (hshort : last.length ≤ width.val)
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes last = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  have hlastLength := _root_.List.length_pos_iff.mpr hlast
  have hpositive : 0 < width.val := by simp only [Slice.length] at hshort; omega
  exact ProgressiveList.from_ssz_bytes_fixed_error ValueInst mapInst bytes width values error
    hfixed hwidth hpositive
    (ssz_items.SszItems.fixed_decodes_final_error ValueInst.sszdecodeDecodeInst.from_ssz_bytes
      encode width values bytes last error hbytes hvalueWidth hdecode hlast hshort herror)
    hlayout hfits updates hdefault

/-- A full-width invalid element returns its exact error, regardless of the
remaining bytes. Only preceding successful elements need codec laws or builder
capacity; later payloads and decoder calls are unconstrained. -/
theorem ProgressiveList.from_ssz_bytes_fixed_element_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes invalid unread : Slice Std.U8) (width : Std.Usize) (hpositive : 0 < width.val)
    (values : _root_.List T) (encode : T → _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode ++ invalid.val ++ unread.val)
    (hvalueWidth : ∀ value ∈ values, (encode value).length = width.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    (hinvalid : invalid.val.length = width.val)
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes invalid = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  exact ProgressiveList.from_ssz_bytes_fixed_error ValueInst mapInst bytes width values error
    hfixed hwidth hpositive
    (ssz_items.SszItems.fixed_decodes_element_error ValueInst.sszdecodeDecodeInst.from_ssz_bytes
      encode width hpositive values bytes invalid unread error hbytes hvalueWidth hdecode
      hinvalid herror) hlayout hfits updates hdefault

end milhouse.progressive_list
