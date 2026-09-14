import Tree.Ssz.FixedCursor

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

/-- Prepending complete fixed-width encodings preserves the suffix's exact
decoded values and stopping error. Decoder laws are required only for the
prepended values; nothing after the stopping point is constrained. -/
theorem SszItems.fixed_decodes_prefix {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (width : Std.Usize) (hpositive : 0 < width.val)
    (values suffixValues : _root_.List T) (bytes suffix : Slice Std.U8)
    (error : Option ssz.decode.DecodeError)
    (hbytes : bytes.val = values.flatMap encode ++ suffix.val)
    (hwidth : ∀ value ∈ values, (encode value).length = width.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value))
    (hsuffix : (.Fixed suffix width : SszItems).Decodes decode suffixValues error) :
    (.Fixed bytes width : SszItems).Decodes decode (values ++ suffixValues) error := by
  induction values generalizing bytes with
  | nil =>
    have heq : bytes = suffix := Slice.ext _ _ (by simpa using hbytes)
    simpa only [heq, _root_.List.nil_append] using hsuffix
  | cons value values ih =>
    have hhead := hwidth value (by simp)
    have hpartBound : (encode value).length ≤ Std.Usize.max := by rw [hhead]; scalar_tac
    have hrestBound : (values.flatMap encode ++ suffix.val).length ≤ Std.Usize.max := by
      have hb := bytes.property
      rw [hbytes] at hb
      simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hb ⊢
      omega
    let part : Slice Std.U8 := Slice.from (encode value) hpartBound
    let rest : Slice Std.U8 := Slice.from (values.flatMap encode ++ suffix.val) hrestBound
    exact .cons
      (SszItems.next_fixed_full bytes part rest width
        (by simpa only [part, rest, Slice.from_val, _root_.List.flatMap_cons, _root_.List.append_assoc] using hbytes)
        (by simpa [part] using hhead) hpositive)
      (hdecode value (by simp) part (by simp [part]))
      (ih rest (by simp [rest]) (fun value hv => hwidth value (by simp [hv]))
        (fun value hv => hdecode value (by simp [hv])))

/-- A nonempty final chunk at most one element wide is passed unchanged to
the element decoder. Its error follows all preceding successful values, even
when the chunk is shorter than the declared width. -/
theorem SszItems.fixed_decodes_final_error {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (width : Std.Usize)
    (values : _root_.List T) (bytes last : Slice Std.U8) (error : ssz.decode.DecodeError)
    (hbytes : bytes.val = values.flatMap encode ++ last.val)
    (hwidth : ∀ value ∈ values, (encode value).length = width.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value))
    (hlast : last.val ≠ []) (hshort : last.length ≤ width.val)
    (herror : decode last = ok (core.result.Result.Err error)) :
    (.Fixed bytes width : SszItems).Decodes decode values (some error) := by
  have hpositive : 0 < width.val := by
    have hlength := _root_.List.length_pos_iff.mpr hlast
    simp only [Slice.length] at hshort
    omega
  simpa only [_root_.List.append_nil] using SszItems.fixed_decodes_prefix decode encode width
    hpositive values [] bytes last (some error) hbytes hwidth hdecode
    (.element_error (SszItems.next_fixed_short last width hlast hshort) herror)

/-- A full-width invalid element stops decoding before any following bytes
are consulted, retaining exactly the preceding successful values. -/
theorem SszItems.fixed_decodes_element_error {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (width : Std.Usize) (hpositive : 0 < width.val)
    (values : _root_.List T) (bytes invalid unread : Slice Std.U8) (error : ssz.decode.DecodeError)
    (hbytes : bytes.val = values.flatMap encode ++ invalid.val ++ unread.val)
    (hwidth : ∀ value ∈ values, (encode value).length = width.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value))
    (hinvalid : invalid.val.length = width.val)
    (herror : decode invalid = ok (core.result.Result.Err error)) :
    (.Fixed bytes width : SszItems).Decodes decode values (some error) := by
  have hsuffixBound : (invalid.val ++ unread.val).length ≤ Std.Usize.max := by
    have hb := bytes.property
    rw [hbytes] at hb
    simp only [_root_.List.length_append] at hb ⊢
    omega
  let suffix : Slice Std.U8 := Slice.from (invalid.val ++ unread.val) hsuffixBound
  simpa only [_root_.List.append_nil] using SszItems.fixed_decodes_prefix decode encode width
    hpositive values [] bytes suffix (some error)
    (by simpa only [suffix, Slice.from_val, _root_.List.append_assoc] using hbytes) hwidth hdecode
    (.element_error (SszItems.next_fixed_full suffix invalid unread width (by simp [suffix]) hinvalid hpositive)
      herror)

end milhouse.ssz_items
