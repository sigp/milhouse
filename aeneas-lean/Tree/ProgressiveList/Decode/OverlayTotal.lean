import Tree.ProgressiveList.Decode.Conditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree milhouse.ssz_items

namespace milhouse.progressive_list

/-- A complete input-bound payload trace, occupied capacity, and actual
default-map success derive public decoding with the exact stored sequence,
length, map, and valid backing. Empty bytes bypass packing and metadata laws;
no public or intermediate construction success is assumed. -/
theorem ProgressiveList.from_ssz_bytes_trace_total {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (entries : _root_.List (T × _root_.List Std.U8))
    (htrace : SszItems.DecodesBytes ValueInst.sszdecodeDecodeInst bytes entries)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor entries.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (.Ok self) ∧ self.tree.elements = entries.map Prod.fst ∧
      self.length.val = entries.length ∧ self.updates = updates ∧ self.BackingValid factor := by
  obtain ⟨self, hdecode⟩ := (ProgressiveList.from_ssz_bytes_success_iff
    ValueInst mapInst bytes hlayout).mpr ⟨entries, htrace, hfits, updates, hdefault⟩
  obtain ⟨helements, hlength, hmap⟩ := ProgressiveList.from_ssz_bytes_trace_contents
    ValueInst mapInst bytes entries htrace hdecode
  have hbacking : self.BackingValid factor := by
    rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
      ⟨_, hempty⟩ | ⟨hnonempty, _⟩
    · exact ProgressiveList.empty_backing_valid ValueInst mapInst factor hempty
    · exact (ProgressiveList.from_ssz_bytes_backing ValueInst mapInst bytes (hlayout hnonempty) hdecode).1
  exact ⟨self, hdecode, helements, hlength, (Result.ok.inj (hmap.symm.trans hdefault)), hbacking⟩

/-- Successful decoding represents its actual decoded sequence exactly when
there is a complete payload trace with occupied capacity and an actual default
map preserving that trace's values through overlay and extent. The forward
direction recovers the consumed payloads; neither a trace nor map success nor
pending emptiness is assumed as a premise. -/
theorem ProgressiveList.from_ssz_bytes_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (.Ok self) ∧ self.Represents ValueInst mapInst self.tree.elements) ↔
    ∃ entries : _root_.List (T × _root_.List Std.U8),
      SszItems.DecodesBytes ValueInst.sszdecodeDecodeInst bytes entries ∧
      ProgressiveTree.LengthFits factor entries.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
        (∃ largest, mapInst.max_index updates = ok largest ∧
          largest.elim entries.length (fun index => max (index.val + 1) entries.length) = entries.length) ∧
        ProgressiveListIter.Overlay mapInst updates (entries.map Prod.fst) (entries.map Prod.fst) := by
  constructor
  · rintro ⟨self, hdecode, hrep⟩
    obtain ⟨entries, htrace, helements, hlength, hdefault⟩ :=
      ProgressiveList.from_ssz_bytes_trace ValueInst mapInst bytes hdecode
    have hfits : ProgressiveTree.LengthFits factor entries.length := by
      rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
        ⟨_, hempty⟩ | ⟨hnonempty, _⟩
      · have hzero := (ProgressiveList.empty_success_state ValueInst mapInst hempty).2.1
        have hentries : entries.length = 0 := by simpa [hzero] using hlength.symm
        rw [hentries]
        exact ProgressiveTree.LengthFits.zero factor
      · have hbacking := (ProgressiveList.from_ssz_bytes_backing
          ValueInst mapInst bytes (hlayout hnonempty) hdecode).1
        rw [← hlength]
        exact hbacking.1.lengthFits hbacking.2
    refine ⟨entries, htrace, hfits, self.updates, hdefault, ?_⟩
    simpa only [helements, _root_.List.length_map] using
      (ProgressiveList.from_ssz_bytes_represents_iff ValueInst mapInst bytes hlayout hdecode).mp hrep
  · rintro ⟨entries, htrace, hfits, updates, hdefault, hextent, hoverlay⟩
    obtain ⟨self, hdecode, helements, _, hupdates, _⟩ :=
      ProgressiveList.from_ssz_bytes_trace_total ValueInst mapInst bytes entries htrace hlayout hfits updates hdefault
    refine ⟨self, hdecode,
      (ProgressiveList.from_ssz_bytes_represents_iff ValueInst mapInst bytes hlayout hdecode).mpr ?_⟩
    simpa only [hupdates, helements, _root_.List.length_map] using And.intro hextent hoverlay

/-- Total public decoding preserves the supplied actual payload sequence
under the exact default-map overlay and extent laws. All execution and backing
results are derived. A separate emptiness law supplies only the pending
observer and is not needed by the sequence criterion above. -/
theorem ProgressiveList.from_ssz_bytes_trace_total_spec_of_overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (entries : _root_.List (T × _root_.List Std.U8))
    (htrace : SszItems.DecodesBytes ValueInst.sszdecodeDecodeInst bytes entries)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor entries.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim entries.length (fun index => max (index.val + 1) entries.length) = entries.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates (entries.map Prod.fst) (entries.map Prod.fst))
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (.Ok self) ∧ self.Represents ValueInst mapInst (entries.map Prod.fst) ∧
      self.BackingValid factor ∧ self.tree.elements = entries.map Prod.fst ∧
      self.length.val = entries.length ∧ self.updates = updates ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hdecode, helements, hlength, hupdates, hbacking⟩ :=
    ProgressiveList.from_ssz_bytes_trace_total ValueInst mapInst bytes entries htrace hlayout hfits updates hdefault
  have hrep := (ProgressiveList.from_ssz_bytes_represents_iff ValueInst mapInst bytes hlayout hdecode).mpr
    (by simpa only [hupdates, helements, _root_.List.length_map] using And.intro hextent hoverlay)
  exact ⟨self, hdecode, by simpa only [helements] using hrep, hbacking,
    helements, hlength, hupdates, ProgressiveList.has_pending_updates_spec ValueInst mapInst self true
      (by simpa only [hupdates] using hempty)⟩

end milhouse.progressive_list
