import Tree.ProgressiveList.Decode.Success
import Tree.Ssz.PayloadSuccess

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Variable-format decoding represents the values of independently accepted
payload occurrences, including empty payloads and different encodings of equal
values. The offset table supplies all builder capacities; only stored offsets
need 32-bit bounds. Empty input bypasses element metadata and packing laws. -/
theorem ProgressiveList.from_ssz_bytes_variable_payloads_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (entries : _root_.List (T × _root_.List Std.U8))
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding Prod.snd entries)
    (hvariable : entries ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hoffsets : _root_.ssz.encode.OffsetsFit Prod.snd (4 * entries.length) entries)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok entry.1))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : entries ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst (entries.map Prod.fst) ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  cases entries with
  | nil =>
    have hemptyBytes : bytes.val = [] := by
      simpa only [_root_.ssz.encode.variableEncoding, _root_.ssz.encode.offsets,
        _root_.List.flatMap_nil, _root_.List.append_nil] using hbytes
    obtain ⟨self, hself, hrep⟩ := ProgressiveList.empty_represents ValueInst mapInst updates hdefault hget hmax
    refine ⟨self, ?_, hrep, ProgressiveList.empty_backing_valid ValueInst mapInst factor hself, ?_⟩
    · rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes hemptyBytes, hself]
      rfl
    · rw [ProgressiveList.empty_eq ValueInst mapInst updates hdefault] at hself
      cases hself
      exact ProgressiveList.has_pending_updates_spec ValueInst mapInst _ true hempty
  | cons entry entries =>
    have hne : entry :: entries ≠ [] := by simp
    have hnonempty : bytes.val ≠ [] := by
      intro hemptyBytes
      have hlen := congrArg _root_.List.length hbytes
      simp only [hemptyBytes, _root_.List.length_nil, _root_.ssz.encode.variableEncoding_length,
        _root_.List.length_cons] at hlen
      omega
    have hfits : ProgressiveTree.LengthFits factor ((entry :: entries).map Prod.fst).length := by
      rw [_root_.List.length_map]
      apply ProgressiveTree.LengthFits.of_four_mul_le_max
      have hlen := bytes.property
      rw [hbytes, _root_.ssz.encode.variableEncoding_length] at hlen
      omega
    obtain ⟨items, hinit, hitems⟩ := ssz_items.SszItems.variable_decodes_payloads
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes (entry :: entries) bytes hne hbytes hoffsets hdecode
    obtain ⟨self, hbuilt, helements, _, hupdates, hvalid⟩ := ProgressiveList.decode_ssz_items_total_spec
      ValueInst mapInst items ((entry :: entries).map Prod.fst) none hitems (hlayout hne) hfits updates hdefault
    refine ⟨self, ?_, ?_, hvalid, ?_⟩
    · simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
        hnonempty, hvariable hne, hinit, core.result.Result.Insts.CoreOpsTry.branch, hbuilt,
        core.result.Result.map_err]
    · rw [← helements]
      exact ProgressiveList.represents_of_dense_backing ValueInst mapInst (hlayout hne) self hvalid.1 hvalid.2
        (by simpa only [hupdates] using hget) (by simpa only [hupdates] using hmax)
    · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst self true
        (by simpa only [hupdates] using hempty)

end milhouse.progressive_list
