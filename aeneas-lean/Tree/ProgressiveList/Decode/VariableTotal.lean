import Tree.ProgressiveList.Decode.Variable
import Tree.ProgressiveList.Decode.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Canonical variable-element bytes decode successfully, including empty
lists and zero-byte payloads. Only offsets actually emitted need a 32-bit
bound; the input offset table supplies every builder rollover check. Empty
input requires no element metadata or packing layout. -/
theorem ProgressiveList.from_ssz_bytes_variable_total {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (hvariable : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding encode values)
    (hoffsets : _root_.ssz.encode.OffsetsFit encode (4 * values.length) values)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : values ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) := by
  cases values with
  | nil =>
    have hempty : bytes.val = [] := by
      simpa only [_root_.ssz.encode.variableEncoding, _root_.ssz.encode.offsets,
        _root_.List.flatMap_nil, _root_.List.append_nil] using hbytes
    refine ⟨{ tree := .ProgressiveZero, length := 0#usize, updates }, ?_⟩
    rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes hempty,
      ProgressiveList.empty_eq ValueInst mapInst updates hdefault]
    rfl
  | cons value values =>
    have hne : value :: values ≠ [] := by simp
    specialize hvariable hne
    specialize hlayout hne
    have hnonempty : bytes.val ≠ [] := by
      intro hempty
      have hlength := congrArg _root_.List.length hbytes
      simp only [hempty, _root_.List.length_nil, _root_.ssz.encode.variableEncoding_length,
        _root_.List.length_cons] at hlength
      omega
    have hfits : ProgressiveTree.LengthFits factor (value :: values).length :=
      ProgressiveTree.LengthFits.of_four_mul_le_max factor (by
        have hlength := bytes.property
        rw [hbytes, _root_.ssz.encode.variableEncoding_length] at hlength
        omega)
    obtain ⟨items, hinit, hitems⟩ := ssz_items.SszItems.variable_decodes_values
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode (value :: values) bytes
      (by simp) hbytes hoffsets hdecodeElement
    obtain ⟨self, hdecode⟩ := ProgressiveList.decode_ssz_items_success ValueInst mapInst
      items (value :: values) none hitems hlayout hfits updates hdefault
    refine ⟨self, ?_⟩
    simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
      hnonempty, hvariable, hinit, core.result.Result.Insts.CoreOpsTry.branch, hdecode,
      core.result.Result.map_err]

/-- Total variable-format decoding reconstructs the exact indexed sequence
with valid backing and no pending updates. Payload decoder laws apply only to
the supplied values, and no builder, cursor, or termination premise is exposed.
Element metadata and packing layout are required only for nonempty input. -/
theorem ProgressiveList.from_ssz_bytes_variable_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (hvariable : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding encode values)
    (hoffsets : _root_.ssz.encode.OffsetsFit encode (4 * values.length) values)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : values ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hdecode⟩ := ProgressiveList.from_ssz_bytes_variable_total ValueInst mapInst bytes values
    encode hvariable hbytes hoffsets hdecodeElement hlayout updates hdefault
  refine ⟨self, hdecode, ProgressiveList.from_ssz_bytes_variable_spec ValueInst mapInst bytes values
    encode hvariable hbytes hoffsets hdecodeElement hlayout ?_ hdecode⟩
  intro actual hactual
  rw [hdefault] at hactual
  cases Result.ok.inj hactual
  exact ⟨hget, hmax, hempty⟩

end milhouse.progressive_list
