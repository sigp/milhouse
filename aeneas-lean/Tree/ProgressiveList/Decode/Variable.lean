import Tree.ProgressiveList.Decode.PublicTrace
import Tree.ProgressiveList.Decode.Contents
import Tree.Ssz.VariableCursor

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_list

/-- Successful variable-format decoding reconstructs the encoded sequence,
including zero-byte element payloads and the empty list. Cursor validity and
arithmetic bounds follow from the canonical bytes and their slice bound.
Element metadata is needed only for nonempty input. -/
theorem ProgressiveList.from_ssz_bytes_variable_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (hvariable : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding encode values)
    (hfit : _root_.ssz.encode.OffsetsFit encode (4 * values.length) values)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    self.tree.elements = values ∧ self.length.val = values.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  cases values with
  | nil =>
    have hemptyBytes : bytes.val = [] := by
      simpa only [_root_.ssz.encode.variableEncoding, _root_.ssz.encode.offsets,
        _root_.List.flatMap_nil, _root_.List.append_nil] using hbytes
    rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes hemptyBytes,
      bind_eq_ok_iff] at hdecode
    obtain ⟨result, hempty, heq⟩ := hdecode
    simp only [ok.injEq, core.result.Result.Ok.injEq] at heq
    cases heq
    obtain ⟨htree, hlength, hdefault⟩ := ProgressiveList.empty_success_state ValueInst mapInst hempty
    exact ⟨by simp [htree, progressive_tree.ProgressiveTree.elements], by simp [hlength], hdefault⟩
  | cons value values =>
    have hne : value :: values ≠ [] := by simp
    specialize hvariable hne
    have hnonempty : bytes.val ≠ [] := by
      intro hempty
      have hlen := congrArg _root_.List.length hbytes
      simp only [hempty, _root_.List.length_nil, _root_.ssz.encode.variableEncoding_length,
        _root_.List.length_cons] at hlen
      omega
    obtain ⟨items, hinit, hitems⟩ := ssz_items.SszItems.variable_decodes_values
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode (value :: values) bytes
      (by simp) hbytes hfit hdecodeElement
    have hbuild := ProgressiveList.from_ssz_bytes_variable_success
      ValueInst mapInst bytes items hnonempty hvariable hinit hdecode
    obtain ⟨helements, hlength, hdefault, _⟩ := ProgressiveList.decode_ssz_items_contents
      ValueInst mapInst items (value :: values) none hitems hbuild
    exact ⟨helements, hlength, hdefault⟩

/-- Sequence-level partial correctness of the public variable-element SSZ
decoder: exact indexed reads, traversal-valid backing, and no pending updates.
The element laws apply only to represented values and their exact payloads.
Element metadata and packing layout are conditional on nonempty input. -/
theorem ProgressiveList.from_ssz_bytes_variable_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (hvariable : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding encode values)
    (hfit : _root_.ssz.encode.OffsetsFit encode (4 * values.length) values)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : values ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ index, mapInst.get updates index = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    self.Represents ValueInst mapInst values ∧ self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨helements, _, _⟩ := ProgressiveList.from_ssz_bytes_variable_contents
    ValueInst mapInst bytes values encode hvariable hbytes hfit hdecodeElement hdecode
  have hlayoutBytes : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth := by
    intro hnonempty
    apply hlayout
    intro hvalues
    apply hnonempty
    simpa [hvalues, _root_.ssz.encode.variableEncoding, _root_.ssz.encode.offsets] using hbytes
  simpa only [helements] using ProgressiveList.from_ssz_bytes_represents
    ValueInst mapInst bytes hlayoutBytes hdefault hdecode

end milhouse.progressive_list
