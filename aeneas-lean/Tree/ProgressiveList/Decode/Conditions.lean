import Tree.ProgressiveList.Decode.PublicTrace
import Tree.ProgressiveList.Decode.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree milhouse.ssz_items

namespace milhouse.progressive_list

/-- Public decoding succeeds exactly when its input has a complete payload
trace, the decoded sequence fits the occupied backing layers, and the actual
default-map call succeeds. The trace contains only parser and element calls;
every list/builder call and internal arithmetic check is derived. Packing
layout is needed only for nonempty input, and no map-content or codec law is
required by this success criterion. -/
theorem ProgressiveList.from_ssz_bytes_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) ↔
    ∃ entries : _root_.List (T × _root_.List Std.U8),
      SszItems.DecodesBytes ValueInst.sszdecodeDecodeInst bytes entries ∧
      ProgressiveTree.LengthFits factor entries.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates := by
  constructor
  · rintro ⟨self, hdecode⟩
    obtain ⟨entries, htrace, _, hlength, hdefault⟩ :=
      ProgressiveList.from_ssz_bytes_trace ValueInst mapInst bytes hdecode
    refine ⟨entries, htrace, ?_, self.updates, hdefault⟩
    rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
      ⟨_, hconstructed⟩ | ⟨hnonempty, _⟩
    · have hzero := (ProgressiveList.empty_success_state ValueInst mapInst hconstructed).2.1
      have hentries : entries.length = 0 := by simpa [hzero] using hlength.symm
      rw [hentries]
      exact ProgressiveTree.LengthFits.zero factor
    · obtain ⟨hbacking, _⟩ := ProgressiveList.from_ssz_bytes_backing
        ValueInst mapInst bytes (hlayout hnonempty) hdecode
      rw [← hlength]
      exact hbacking.1.lengthFits hbacking.2
  · rintro ⟨entries, htrace, hfits, updates, hdefault⟩
    cases htrace with
    | empty hbytes =>
      refine ⟨{ tree := .ProgressiveZero, length := 0#usize, updates }, ?_⟩
      rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes hbytes,
        ProgressiveList.empty_eq ValueInst mapInst updates hdefault]
      rfl
    | @fixed width entries hnonempty hfixed hwidth hnonzero htrace =>
      obtain ⟨self, hbuild⟩ := ProgressiveList.decode_ssz_items_success
        ValueInst mapInst (.Fixed bytes width) (entries.map Prod.fst) none
        (htrace.forget_payload _ _ _ _) (hlayout hnonempty)
        (by simpa using hfits) updates hdefault
      refine ⟨self, ?_⟩
      simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
        hnonempty, hfixed, hwidth, hnonzero, hbuild, core.result.Result.map_err]
    | @«variable» items entries hnonempty hvariable hitems htrace =>
      obtain ⟨self, hbuild⟩ := ProgressiveList.decode_ssz_items_success
        ValueInst mapInst items (entries.map Prod.fst) none
        (htrace.forget_payload _ _ _ _) (hlayout hnonempty)
        (by simpa using hfits) updates hdefault
      refine ⟨self, ?_⟩
      simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
        hnonempty, hvariable, hitems, hbuild, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.map_err]

end milhouse.progressive_list
