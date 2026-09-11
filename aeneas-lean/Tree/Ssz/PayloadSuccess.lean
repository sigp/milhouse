import Tree.Ssz.PayloadTrace
import Tree.Ssz.FixedPrefix
import Tree.Ssz.VariableCursor

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

/-- Fixed-width decoding accepts each occurrence's own payload. Equal values
may have distinct accepted encodings; only the supplied slices are decoded. -/
theorem SszItems.fixed_decodes_payloads {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (width : Std.Usize) (hpositive : 0 < width.val)
    (entries : _root_.List (T × _root_.List Std.U8)) (bytes : Slice Std.U8)
    (hbytes : bytes.val = entries.flatMap Prod.snd)
    (hwidth : ∀ entry ∈ entries, entry.2.length = width.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → decode part = ok (core.result.Result.Ok entry.1)) :
    (.Fixed bytes width : SszItems).Decodes decode (entries.map Prod.fst) none := by
  apply SszItems.Decodes.forget_payload decode
  exact SszItems.fixed_decodes_values (SszItems.recordPayload decode) Prod.snd width hpositive
    entries bytes hbytes hwidth (fun entry he part hp =>
      (SszItems.recordPayload_ok_iff decode part entry).mpr ⟨hdecode entry he part hp, hp⟩)

/-- A nonempty final chunk at most one declared width is accepted whenever
the element decoder accepts that exact chunk. It follows the full-width
payload prefix, even when its actual width is smaller than the declared one. -/
theorem SszItems.fixed_decodes_final_payload {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (width : Std.Usize) (entries : _root_.List (T × _root_.List Std.U8))
    (bytes last : Slice Std.U8) (lastValue : T)
    (hbytes : bytes.val = entries.flatMap Prod.snd ++ last.val)
    (hwidth : ∀ entry ∈ entries, entry.2.length = width.val)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → decode part = ok (core.result.Result.Ok entry.1))
    (hlast : last.val ≠ []) (hshort : last.length ≤ width.val)
    (hdecodedLast : decode last = ok (core.result.Result.Ok lastValue)) :
    (.Fixed bytes width : SszItems).Decodes decode (entries.map Prod.fst ++ [lastValue]) none := by
  have hpositive : 0 < width.val := by
    have hlength := _root_.List.length_pos_iff.mpr hlast
    simp only [Slice.length] at hshort
    omega
  have hsuffix : (.Fixed last width : SszItems).Decodes (SszItems.recordPayload decode)
      [(lastValue, last.val)] none :=
    .cons (SszItems.next_fixed_short last width hlast hshort)
      ((SszItems.recordPayload_ok_iff decode last (lastValue, last.val)).mpr ⟨hdecodedLast, rfl⟩)
      (.exhausted (SszItems.next_fixed_empty _ width rfl))
  have htrace := SszItems.fixed_decodes_prefix (SszItems.recordPayload decode) Prod.snd width hpositive
    entries [(lastValue, last.val)] bytes last none hbytes hwidth
    (fun entry he part hp => (SszItems.recordPayload_ok_iff decode part entry).mpr
      ⟨hdecode entry he part hp, hp⟩) hsuffix
  simpa only [_root_.List.map_append, _root_.List.map_cons, _root_.List.map_nil] using
    SszItems.Decodes.forget_payload decode _ _ _ htrace

/-- A valid variable offset table decodes its per-occurrence payloads in
order, including empty payloads and different encodings of equal values.
Only stored offsets need 32-bit bounds; the final payload end needs none. -/
theorem SszItems.variable_decodes_payloads {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (entries : _root_.List (T × _root_.List Std.U8)) (bytes : Slice Std.U8)
    (hnonempty : entries ≠ [])
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding Prod.snd entries)
    (hfit : _root_.ssz.encode.OffsetsFit Prod.snd (4 * entries.length) entries)
    (hdecode : ∀ entry ∈ entries, ∀ part : Slice Std.U8,
      part.val = entry.2 → decode part = ok (core.result.Result.Ok entry.1)) :
    ∃ items, SszItems.variable bytes = ok (core.result.Result.Ok items) ∧
      items.Decodes decode (entries.map Prod.fst) none := by
  obtain ⟨items, hinit, htrace⟩ := SszItems.variable_decodes_values
    (SszItems.recordPayload decode) Prod.snd entries bytes hnonempty hbytes hfit
    (fun entry he part hp => (SszItems.recordPayload_ok_iff decode part entry).mpr
      ⟨hdecode entry he part hp, hp⟩)
  exact ⟨items, hinit, SszItems.Decodes.forget_payload decode _ _ _ htrace⟩

end milhouse.ssz_items
