import Tree.ProgressiveList.Decode.Fixed
import Tree.ProgressiveList.Decode.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Canonical fixed-element bytes decode successfully when their sequence
fits the progressive layers and the actual default-map call succeeds. Cursor
termination, every builder call, and internal arithmetic are derived. Empty
input needs no element metadata, positive width, layout, or capacity premise. -/
theorem ProgressiveList.from_ssz_bytes_fixed_total {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (width : Std.Usize) (hpositive : values ≠ [] → 0 < width.val)
    (hfixed : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : values ≠ [] → ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode)
    (hsize : ∀ value ∈ values, (encode value).length = width.val)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : values ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : values ≠ [] → ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) := by
  cases values with
  | nil =>
    refine ⟨{ tree := .ProgressiveZero, length := 0#usize, updates }, ?_⟩
    rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes (by simpa using hbytes),
      ProgressiveList.empty_eq ValueInst mapInst updates hdefault]
    rfl
  | cons value values =>
    have hne : value :: values ≠ [] := by simp
    specialize hpositive hne
    specialize hfixed hne
    specialize hwidth hne
    specialize hlayout hne
    specialize hfits hne
    have hnonempty : bytes.val ≠ [] := by
      intro hempty
      have hhead := hsize value (by simp)
      have hlength := congrArg _root_.List.length hbytes
      simp only [hempty, _root_.List.length_nil, _root_.List.flatMap_cons,
        _root_.List.length_append, hhead] at hlength
      omega
    have hitems := ssz_items.SszItems.fixed_decodes_values
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode width hpositive
      (value :: values) bytes hbytes hsize hdecodeElement
    obtain ⟨self, hdecode⟩ := ProgressiveList.decode_ssz_items_success ValueInst mapInst
      (.Fixed bytes width) (value :: values) none hitems hlayout hfits updates hdefault
    have hwidthNe : width ≠ 0#usize := by
      intro hzero
      have hval := congrArg UScalar.val hzero
      change width.val = 0 at hval
      omega
    refine ⟨self, ?_⟩
    simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
      hnonempty, hfixed, hwidth, hwidthNe, hdecode, core.result.Result.map_err]

/-- Total fixed-format decoding preserves the input sequence under the
actual default map's exact overlay and extent laws. Redundant matching entries
are permitted. Empty input bypasses element metadata and packing laws; pending
emptiness is a separate law used only for its observer. -/
theorem ProgressiveList.from_ssz_bytes_fixed_total_spec_of_overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (width : Std.Usize) (hpositive : values ≠ [] → 0 < width.val)
    (hfixed : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : values ≠ [] → ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode)
    (hsize : ∀ value ∈ values, (encode value).length = width.val)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : values ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : values ≠ [] → ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates values values)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hdecode⟩ := ProgressiveList.from_ssz_bytes_fixed_total ValueInst mapInst bytes values
    encode width hpositive hfixed hwidth hbytes hsize hdecodeElement hlayout hfits updates hdefault
  obtain ⟨helements, _, hmap⟩ := ProgressiveList.from_ssz_bytes_fixed_contents
    ValueInst mapInst bytes values encode width hpositive hfixed hwidth hbytes hsize hdecodeElement hdecode
  have hupdates : self.updates = updates := Result.ok.inj (hmap.symm.trans hdefault)
  have hlayoutBytes : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth := by
    intro hnonempty
    apply hlayout
    intro hvalues
    apply hnonempty
    simpa [hvalues] using hbytes
  refine ⟨self, hdecode, ?_⟩
  have hspec := ProgressiveList.from_ssz_bytes_spec_of_overlay ValueInst mapInst bytes hlayoutBytes hdecode
    (by simpa only [hupdates, helements] using hextent)
    (by simpa only [hupdates, helements] using hoverlay)
    (by simpa only [hupdates] using hempty)
  simpa only [helements] using hspec

/-- Total fixed-format decoding reconstructs the exact indexed sequence,
with valid backing and no pending updates. Only the consumed element payloads,
their declared width, the packing layout, representable sequence length, and
the actual default map's empty behavior are required. Metadata, positive width,
layout, and capacity premises are conditional on a nonempty sequence. -/
theorem ProgressiveList.from_ssz_bytes_fixed_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (width : Std.Usize) (hpositive : values ≠ [] → 0 < width.val)
    (hfixed : values ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : values ≠ [] → ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode)
    (hsize : ∀ value ∈ values, (encode value).length = width.val)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : values ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : values ≠ [] → ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values ∧
      self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  exact ProgressiveList.from_ssz_bytes_fixed_total_spec_of_overlay ValueInst mapInst bytes values
    encode width hpositive hfixed hwidth hbytes hsize hdecodeElement hlayout hfits updates hdefault
    ⟨none, hmax, rfl⟩ (fun index => ⟨none, hget index, rfl⟩) hempty

end milhouse.progressive_list
