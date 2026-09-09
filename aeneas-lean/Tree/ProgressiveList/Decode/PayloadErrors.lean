import Tree.ProgressiveList.Decode.ErrorResult
import Tree.Ssz.VariablePrefixErrors
import Tree.Ssz.VariableElementErrors
import Tree.Ssz.PayloadTrace
import Tree.Ssz.FixedPrefix

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A malformed variable offset after any accepted payload prefix returns
the exact ordered offset error. Each prefix entry records its own bytes, so
equal values may have different encodings and accepted noncanonical payloads
are supported. No encoding function or canonical-decoder law is assumed. -/
theorem ProgressiveList.from_ssz_bytes_variable_offset_error_of_payloads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (bytes : Slice Std.U8)
    (first count current nextOffset : Std.Usize) (entries : _root_.List (T × _root_.List Std.U8))
    (tableSuffix payloadSuffix : _root_.List Std.U8)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirst : first.val = 4 * count.val) (hcount : entries.length + 1 < count.val)
    (hfirstBound : first.val ≤ bytes.length)
    (hcurrent : current.val = first.val + (entries.flatMap Prod.snd).length)
    (hcurrentFit : current.val ≤ Std.U32.max) (hnextFit : nextOffset.val ≤ Std.U32.max)
    (htable : bytes.val = _root_.ssz.encode.offsets Prod.snd first.val entries ++
      _root_.ssz.encode.offsetBytes current.val ++ _root_.ssz.encode.offsetBytes nextOffset.val ++
        tableSuffix)
    (hpayload : bytes.val.drop first.val = entries.flatMap Prod.snd ++ payloadSuffix)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
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
  let decode := ValueInst.sszdecodeDecodeInst.from_ssz_bytes
  have hread := _root_.ssz.decode.read_offset_prefix Prod.snd bytes first current entries
    (_root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix) hcurrent hcurrentFit
    (by simpa only [_root_.List.append_assoc] using htable)
  have htrace := ssz_items.SszItems.variable_decodes_offset_error
    (ssz_items.SszItems.recordPayload decode) Prod.snd bytes first count current nextOffset entries
    tableSuffix payloadSuffix hfirst hcount hfirstBound hcurrent hcurrentFit hnextFit htable hpayload
    (fun entry he part hp => (ssz_items.SszItems.recordPayload_ok_iff decode part entry).mpr
      ⟨hdecode entry he part hp, hp⟩) hbad
  have hitems := ssz_items.SszItems.Decodes.forget_payload decode _ _ _ htrace
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count
    (entries.map Prod.fst) _ hvariable hread hfirst (by omega) hfirstBound hitems hlayout updates hdefault

/-- A nonfinal variable payload error follows any accepted prefix, including
distinct encodings of equal values. Its offsets are checked first; later bytes
and element decoder behavior are unconstrained. -/
theorem ProgressiveList.from_ssz_bytes_variable_element_error_of_payloads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (bytes part : Slice Std.U8)
    (first count current nextOffset : Std.Usize) (entries : _root_.List (T × _root_.List Std.U8))
    (tableSuffix payloadSuffix : _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirst : first.val = 4 * count.val) (hcount : entries.length + 1 < count.val)
    (hcurrent : current.val = first.val + (entries.flatMap Prod.snd).length)
    (hnextFit : nextOffset.val ≤ Std.U32.max) (hnextBound : nextOffset.val ≤ bytes.length)
    (horder : current.val ≤ nextOffset.val)
    (htable : bytes.val = _root_.ssz.encode.offsets Prod.snd first.val entries ++
      _root_.ssz.encode.offsetBytes current.val ++ _root_.ssz.encode.offsetBytes nextOffset.val ++
        tableSuffix)
    (hpayload : bytes.val.drop first.val = entries.flatMap Prod.snd ++ payloadSuffix)
    (hdecode : ∀ entry ∈ entries, ∀ bytes : Slice Std.U8,
      bytes.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes bytes =
        ok (core.result.Result.Ok entry.1))
    (hpart : part.val = bytes.val.slice current.val nextOffset.val)
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes part = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  let decode := ValueInst.sszdecodeDecodeInst.from_ssz_bytes
  have hread := _root_.ssz.decode.read_offset_prefix Prod.snd bytes first current entries
    (_root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix) hcurrent (by omega)
    (by simpa only [_root_.List.append_assoc] using htable)
  have htrace := ssz_items.SszItems.variable_decodes_element_error
    (ssz_items.SszItems.recordPayload decode) Prod.snd bytes part first count current nextOffset
    entries tableSuffix payloadSuffix error hfirst hcount hcurrent hnextFit hnextBound horder
    htable hpayload
    (fun entry he bytes hp => (ssz_items.SszItems.recordPayload_ok_iff decode bytes entry).mpr
      ⟨hdecode entry he bytes hp, hp⟩) hpart
    ((ssz_items.SszItems.recordPayload_error_iff decode part error).mpr herror)
  have hitems := ssz_items.SszItems.Decodes.forget_payload decode _ _ _ htrace
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count
    (entries.map Prod.fst) error hvariable hread hfirst (by omega) (by omega) hitems hlayout updates hdefault

/-- The final variable payload's error is returned after any accepted prefix,
without requiring a canonical encoding for those values. Empty final payloads
are included, and the complete table supplies all input and capacity bounds. -/
theorem ProgressiveList.from_ssz_bytes_variable_final_error_of_payloads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (bytes last : Slice Std.U8)
    (first count current : Std.Usize) (entries : _root_.List (T × _root_.List Std.U8))
    (tableSuffix : _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hfirst : first.val = 4 * count.val) (hcount : entries.length + 1 = count.val)
    (hcurrent : current.val = first.val + (entries.flatMap Prod.snd).length)
    (hfit : current.val ≤ Std.U32.max)
    (htable : bytes.val = _root_.ssz.encode.offsets Prod.snd first.val entries ++
      _root_.ssz.encode.offsetBytes current.val ++ tableSuffix)
    (hpayload : bytes.val.drop first.val = entries.flatMap Prod.snd ++ last.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes last = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  let decode := ValueInst.sszdecodeDecodeInst.from_ssz_bytes
  have hfirstBound : first.val ≤ bytes.length := by
    have hlen := congrArg _root_.List.length htable
    simp only [_root_.List.length_append, _root_.ssz.encode.offsets_length,
      _root_.ssz.encode.offsetBytes_length] at hlen
    simp only [Slice.length]
    omega
  have hread := _root_.ssz.decode.read_offset_prefix Prod.snd bytes first current entries tableSuffix
    hcurrent hfit htable
  have htrace := ssz_items.SszItems.variable_decodes_final_error
    (ssz_items.SszItems.recordPayload decode) Prod.snd bytes last first count current entries
    tableSuffix error hfirst hcount hcurrent hfit htable hpayload
    (fun entry he part hp => (ssz_items.SszItems.recordPayload_ok_iff decode part entry).mpr
      ⟨hdecode entry he part hp, hp⟩)
    ((ssz_items.SszItems.recordPayload_error_iff decode last error).mpr herror)
  have hitems := ssz_items.SszItems.Decodes.forget_payload decode _ _ _ htrace
  exact ProgressiveList.from_ssz_bytes_variable_error ValueInst mapInst bytes first count
    (entries.map Prod.fst) error hvariable hread hfirst (by omega) hfirstBound hitems hlayout updates hdefault

/-- A fixed-width invalid element follows any accepted payload prefix,
including distinct encodings of equal values. All following bytes are ignored
and capacity is required only for the successfully decoded prefix. -/
theorem ProgressiveList.from_ssz_bytes_fixed_element_error_of_payloads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes invalid unread : Slice Std.U8) (width : Std.Usize) (hpositive : 0 < width.val)
    (entries : _root_.List (T × _root_.List Std.U8)) (error : ssz.decode.DecodeError)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = entries.flatMap Prod.snd ++ invalid.val ++ unread.val)
    (hentryWidth : ∀ entry ∈ entries, entry.2.length = width.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
    (hinvalid : invalid.val.length = width.val)
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes invalid = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : progressive_tree.ProgressiveTree.LengthFits factor entries.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  let decode := ValueInst.sszdecodeDecodeInst.from_ssz_bytes
  have htrace := ssz_items.SszItems.fixed_decodes_element_error
    (ssz_items.SszItems.recordPayload decode) Prod.snd width hpositive entries bytes invalid unread error
    hbytes hentryWidth
    (fun entry he part hp => (ssz_items.SszItems.recordPayload_ok_iff decode part entry).mpr
      ⟨hdecode entry he part hp, hp⟩) hinvalid
    ((ssz_items.SszItems.recordPayload_error_iff decode invalid error).mpr herror)
  have hitems := ssz_items.SszItems.Decodes.forget_payload decode _ _ _ htrace
  exact ProgressiveList.from_ssz_bytes_fixed_error ValueInst mapInst bytes width (entries.map Prod.fst)
    error hfixed hwidth hpositive hitems hlayout
    (by simpa only [_root_.List.length_map] using hfits) updates hdefault

/-- A final fixed-format chunk, including a short chunk, reaches the element
decoder unchanged after any accepted payload prefix. The error is returned
without a canonical-encoding assumption on preceding values. -/
theorem ProgressiveList.from_ssz_bytes_fixed_final_error_of_payloads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes last : Slice Std.U8) (width : Std.Usize)
    (entries : _root_.List (T × _root_.List Std.U8)) (error : ssz.decode.DecodeError)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = entries.flatMap Prod.snd ++ last.val)
    (hentryWidth : ∀ entry ∈ entries, entry.2.length = width.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
    (hlast : last.val ≠ []) (hshort : last.length ≤ width.val)
    (herror : ValueInst.sszdecodeDecodeInst.from_ssz_bytes last = ok (core.result.Result.Err error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : progressive_tree.ProgressiveTree.LengthFits factor entries.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  let decode := ValueInst.sszdecodeDecodeInst.from_ssz_bytes
  have hpositive : 0 < width.val := by
    have hlastLength := _root_.List.length_pos_iff.mpr hlast
    simp only [Slice.length] at hshort
    omega
  have htrace := ssz_items.SszItems.fixed_decodes_final_error
    (ssz_items.SszItems.recordPayload decode) Prod.snd width entries bytes last error hbytes hentryWidth
    (fun entry he part hp => (ssz_items.SszItems.recordPayload_ok_iff decode part entry).mpr
      ⟨hdecode entry he part hp, hp⟩) hlast hshort
    ((ssz_items.SszItems.recordPayload_error_iff decode last error).mpr herror)
  have hitems := ssz_items.SszItems.Decodes.forget_payload decode _ _ _ htrace
  exact ProgressiveList.from_ssz_bytes_fixed_error ValueInst mapInst bytes width (entries.map Prod.fst)
    error hfixed hwidth hpositive hitems hlayout
    (by simpa only [_root_.List.length_map] using hfits) updates hdefault

end milhouse.progressive_list
