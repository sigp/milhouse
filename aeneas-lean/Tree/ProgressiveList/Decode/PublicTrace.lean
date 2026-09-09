import Tree.ProgressiveList.Decode.Trace
import Tree.ProgressiveList.Decode.Backing
import Tree.Ssz.DecodedBytes

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree milhouse.ssz_items

namespace milhouse.progressive_list

/-- Every successful public decoder result reflects a complete input-bound
payload trace, stores exactly its decoded values and count, and installs the
actual default map. No metadata, packing, parser, codec, or map law is assumed.
Empty input uses no element metadata and supplies the empty trace. -/
theorem ProgressiveList.from_ssz_bytes_trace {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    ∃ entries : _root_.List (T × _root_.List Std.U8),
      SszItems.DecodesBytes ValueInst.sszdecodeDecodeInst bytes entries ∧
      self.tree.elements = entries.map Prod.fst ∧ self.length.val = entries.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
    ⟨hbytes, hempty⟩ | ⟨hnonempty, hsource⟩
  · obtain ⟨htree, hlength, hdefault⟩ := ProgressiveList.empty_success_state
      ValueInst mapInst hempty
    exact ⟨[], .empty hbytes, by simp [htree, ProgressiveTree.elements],
      by simp [hlength], hdefault⟩
  · rcases hsource with ⟨width, hfixed, hwidth, hnonzero, hbuild⟩ |
      ⟨hvariable, items, hitems, hbuild⟩
    · obtain ⟨entries, htrace, helements, hlength, hdefault⟩ :=
        ProgressiveList.decode_ssz_items_trace ValueInst mapInst (.Fixed bytes width) hbuild
      exact ⟨entries, .fixed hnonempty hfixed hwidth hnonzero htrace,
        helements, hlength, hdefault⟩
    · obtain ⟨entries, htrace, helements, hlength, hdefault⟩ :=
        ProgressiveList.decode_ssz_items_trace ValueInst mapInst items hbuild
      exact ⟨entries, .variable hnonempty hvariable hitems htrace,
        helements, hlength, hdefault⟩

/-- Every successful decoder result represents its materialized backing
sequence and has no pending updates. This common state contract needs only
empty-default-map laws and packing layout for nonempty input, independently
of the input format or any particular payload trace. -/
theorem ProgressiveList.from_ssz_bytes_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ index, mapInst.get updates index = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    self.Represents ValueInst mapInst self.tree.elements ∧ self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨_, _, _, _, hmap⟩ :=
    ProgressiveList.from_ssz_bytes_trace ValueInst mapInst bytes hdecode
  obtain ⟨hget, hmax, hempty⟩ := hdefault self.updates hmap
  have hpending := ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty
  rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
    ⟨_, hconstructed⟩ | ⟨hnonempty, _⟩
  · have htree := (ProgressiveList.empty_success_state ValueInst mapInst hconstructed).1
    obtain ⟨result, hresult, hrep⟩ := ProgressiveList.empty_represents
      ValueInst mapInst self.updates hmap hget hmax
    rw [hconstructed] at hresult
    cases Result.ok.inj hresult
    exact ⟨by simpa [htree, ProgressiveTree.elements] using hrep,
      ProgressiveList.empty_backing_valid ValueInst mapInst factor hconstructed, hpending⟩
  · obtain ⟨hbacking, _⟩ := ProgressiveList.from_ssz_bytes_backing
      ValueInst mapInst bytes (hlayout hnonempty) hdecode
    exact ⟨ProgressiveList.represents_of_dense_backing ValueInst mapInst (hlayout hnonempty) self
      hbacking.1 hbacking.2 hget hmax, hbacking, hpending⟩

/-- Successful decoding represents the actual payload trace at every index,
with valid backing and no pending updates. Only the actual default map's empty
behavior is needed in addition to packing layout for nonempty input. The
accepted bytes and element results are inferred rather than supplied. -/
theorem ProgressiveList.from_ssz_bytes_trace_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ index, mapInst.get updates index = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    ∃ entries : _root_.List (T × _root_.List Std.U8),
      SszItems.DecodesBytes ValueInst.sszdecodeDecodeInst bytes entries ∧
      self.Represents ValueInst mapInst (entries.map Prod.fst) ∧ self.BackingValid factor ∧
      self.length.val = entries.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨entries, htrace, helements, hlength, hmap⟩ :=
    ProgressiveList.from_ssz_bytes_trace ValueInst mapInst bytes hdecode
  obtain ⟨hrep, hbacking, hpending⟩ := ProgressiveList.from_ssz_bytes_represents
    ValueInst mapInst bytes hlayout hdefault hdecode
  exact ⟨entries, htrace, by simpa only [helements] using hrep,
    hbacking, hlength, hmap, hpending⟩

end milhouse.progressive_list
