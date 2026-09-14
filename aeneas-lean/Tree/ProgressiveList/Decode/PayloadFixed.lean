import Tree.ProgressiveList.Decode.Success
import Tree.Ssz.PayloadSuccess

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

private theorem fixed_payload_trace_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (width : Std.Usize) (values : _root_.List T)
    (hnonempty : bytes.val ≠ []) (hpositive : 0 < width.val)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hitems : (ssz_items.SszItems.Fixed bytes width).Decodes
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes values none)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hdecode, helements, _, hupdates, hvalid⟩ := ProgressiveList.decode_ssz_items_total_spec
    ValueInst mapInst (.Fixed bytes width) values none hitems hlayout hfits updates hdefault
  have hwidthNe : width ≠ 0#usize := by scalar_tac
  refine ⟨self, ?_, ?_, hvalid, ?_⟩
  · simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
      hnonempty, hfixed, hwidth, hwidthNe, hdecode, core.result.Result.map_err]
  · rw [← helements]
    exact ProgressiveList.represents_of_dense_backing ValueInst mapInst hlayout self hvalid.1 hvalid.2
      (by simpa only [hupdates] using hget) (by simpa only [hupdates] using hmax)
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst self true
      (by simpa only [hupdates] using hempty)

/-- Fixed-format decoding represents the values of independently accepted
payload occurrences, including different encodings of equal values. Empty input
needs no metadata, packing, or capacity laws; the actual default map is still
constructed. Cursor and builder success are derived from the input bytes. -/
theorem ProgressiveList.from_ssz_bytes_fixed_payloads_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (entries : _root_.List (T × _root_.List Std.U8)) (width : Std.Usize)
    (hbytes : bytes.val = entries.flatMap Prod.snd)
    (hpositive : entries ≠ [] → 0 < width.val)
    (hfixed : entries ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : entries ≠ [] → ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hentryWidth : ∀ entry ∈ entries, entry.2.length = width.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : entries ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : entries ≠ [] → ProgressiveTree.LengthFits factor entries.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst (entries.map Prod.fst) ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  cases entries with
  | nil =>
    obtain ⟨self, hself, hrep⟩ := ProgressiveList.empty_represents ValueInst mapInst updates hdefault hget hmax
    refine ⟨self, ?_, hrep, ProgressiveList.empty_backing_valid ValueInst mapInst factor hself, ?_⟩
    · rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes (by simpa using hbytes), hself]
      rfl
    · rw [ProgressiveList.empty_eq ValueInst mapInst updates hdefault] at hself
      cases hself
      exact ProgressiveList.has_pending_updates_spec ValueInst mapInst _ true hempty
  | cons entry entries =>
    have hne : entry :: entries ≠ [] := by simp
    have hnonempty : bytes.val ≠ [] := by
      intro hemptyBytes
      have hhead := hentryWidth entry (by simp)
      have hlen := congrArg _root_.List.length hbytes
      simp only [hemptyBytes, _root_.List.length_nil, _root_.List.flatMap_cons,
        _root_.List.length_append, hhead] at hlen
      have := hpositive hne
      omega
    have hitems := ssz_items.SszItems.fixed_decodes_payloads
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes width (hpositive hne) (entry :: entries)
      bytes hbytes hentryWidth hdecode
    exact fixed_payload_trace_spec ValueInst mapInst bytes width _ hnonempty (hpositive hne)
      (hfixed hne) (hwidth hne) hitems (hlayout hne)
      (by simpa only [_root_.List.length_map] using hfits hne) updates hdefault hget hmax hempty

/-- An accepted final fixed-format chunk is included in the represented
sequence even if shorter than the declared element width. Earlier occurrences
have independent full-width payloads; no canonical-encoding law is assumed. -/
theorem ProgressiveList.from_ssz_bytes_fixed_final_payload_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes last : Slice Std.U8) (entries : _root_.List (T × _root_.List Std.U8))
    (lastValue : T) (width : Std.Usize)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = entries.flatMap Prod.snd ++ last.val)
    (hentryWidth : ∀ entry ∈ entries, entry.2.length = width.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
    (hlast : last.val ≠ []) (hshort : last.length ≤ width.val)
    (hdecodedLast : ValueInst.sszdecodeDecodeInst.from_ssz_bytes last = ok (core.result.Result.Ok lastValue))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor (entries.length + 1))
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst (entries.map Prod.fst ++ [lastValue]) ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  have hpositive : 0 < width.val := by
    have hlength := _root_.List.length_pos_iff.mpr hlast
    simp only [Slice.length] at hshort
    omega
  have hnonempty : bytes.val ≠ [] := by simp [hbytes, hlast]
  have hitems := ssz_items.SszItems.fixed_decodes_final_payload
    ValueInst.sszdecodeDecodeInst.from_ssz_bytes width entries bytes last lastValue hbytes hentryWidth
      hdecode hlast hshort hdecodedLast
  exact fixed_payload_trace_spec ValueInst mapInst bytes width _ hnonempty hpositive hfixed hwidth
    hitems hlayout (by simpa only [_root_.List.length_append, _root_.List.length_map,
      _root_.List.length_cons, _root_.List.length_nil] using hfits) updates hdefault hget hmax hempty

end milhouse.progressive_list
