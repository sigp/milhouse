import Tree.Ssz.DecodedItems

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

theorem SszItems.next_fixed_empty (bytes : Slice Std.U8) (width : Std.Usize)
    (hempty : bytes.val = []) :
    SszItems.next (.Fixed bytes width) = ok (none, .Fixed bytes width) := by
  simp [SszItems.next, core.slice.Slice.is_empty, hempty]

/-- A complete fixed-width payload is yielded unchanged, leaving exactly the
following bytes. There is no copying or element decoding in this operation. -/
theorem SszItems.next_fixed_full (bytes part rest : Slice Std.U8) (width : Std.Usize)
    (hbytes : bytes.val = part.val ++ rest.val) (hwidth : part.val.length = width.val)
    (hpositive : 0 < width.val) :
    SszItems.next (.Fixed bytes width) =
      ok (some (core.result.Result.Ok part), .Fixed rest width) := by
  have hbound : width.val ≤ bytes.length := by simp [Slice.length, hbytes, hwidth]
  have hnonempty : bytes.val ≠ [] := by
    intro h
    have : bytes.val.length = 0 := by simp [h]
    simp only [hbytes, _root_.List.length_append, hwidth] at this
    omega
  have hmin : core.cmp.min core.cmp.OrdUsize width bytes.len = ok width := by
    change ok (if width < bytes.len then width else bytes.len) = ok width
    split
    · rfl
    · congr 1
      apply UScalar.eq_of_val_eq
      simp only [UScalar.lt_equiv, Slice.len_val] at *
      omega
  have hsplit : core.slice.Slice.split_at bytes width = ok (part, rest) := by
    simp only [core.slice.Slice.split_at, hbound, ↓reduceDIte, _root_.List.splitAt_eq]
    congr 1
    apply Prod.ext <;> apply Subtype.ext
    · simp [hbytes, ← hwidth]
    · simp [hbytes, ← hwidth]
  have hempty : core.slice.Slice.is_empty bytes = ok false := by
    simp [core.slice.Slice.is_empty, hnonempty]
  simp! only [SszItems.next, hempty, hmin, hsplit, bind_tc_ok] <;> rfl

/-- A short final payload is passed through to the element decoder; the
cursor does not replace the element decoder's error with an alignment error. -/
theorem SszItems.next_fixed_short (bytes : Slice Std.U8) (width : Std.Usize)
    (hnonempty : bytes.val ≠ []) (hshort : bytes.length ≤ width.val) :
    SszItems.next (.Fixed bytes width) =
      ok (some (core.result.Result.Ok bytes), .Fixed (⟨[], by simp⟩ : Slice Std.U8) width) := by
  have hmin : core.cmp.min core.cmp.OrdUsize width bytes.len = ok bytes.len := by
    change ok (if width < bytes.len then width else bytes.len) = ok bytes.len
    have hnot : ¬ width < bytes.len := by
      simp only [UScalar.lt_equiv, Slice.len_val]
      omega
    rw [if_neg hnot]
  have hsplit : core.slice.Slice.split_at bytes bytes.len =
      ok (bytes, (⟨[], by simp⟩ : Slice Std.U8)) := by
    simp only [core.slice.Slice.split_at, Slice.len_val, le_refl, ↓reduceDIte,
      _root_.List.splitAt_eq]
    congr 1
    apply Prod.ext <;> apply Subtype.ext <;> simp [Slice.length]
  have hempty : core.slice.Slice.is_empty bytes = ok false := by
    simp [core.slice.Slice.is_empty, hnonempty]
  simp! only [SszItems.next, hempty, hmin, hsplit, bind_tc_ok] <;> rfl

/-- Concatenated fixed-size encodings are streamed in their original order.
Element decoding is required only on these values and these exact byte slices. -/
theorem SszItems.fixed_decodes_values {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (width : Std.Usize) (hpositive : 0 < width.val)
    (values : _root_.List T) (bytes : Slice Std.U8)
    (hbytes : bytes.val = values.flatMap encode)
    (hwidth : ∀ value ∈ values, (encode value).length = width.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value)) :
    (.Fixed bytes width : SszItems).Decodes decode values none := by
  induction values generalizing bytes with
  | nil =>
    exact .exhausted (SszItems.next_fixed_empty bytes width (by simpa using hbytes))
  | cons value values ih =>
    have hhead := hwidth value (by simp)
    have hpartBound : (encode value).length ≤ Std.Usize.max := by rw [hhead]; scalar_tac
    have hrestBound : (values.flatMap encode).length ≤ Std.Usize.max := by
      have hb := bytes.property
      rw [hbytes] at hb
      simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hb
      omega
    let part : Slice Std.U8 := ⟨encode value, hpartBound⟩
    let rest : Slice Std.U8 := ⟨values.flatMap encode, hrestBound⟩
    exact .cons
      (SszItems.next_fixed_full bytes part rest width (by simpa [part, rest] using hbytes)
        hhead hpositive)
      (hdecode value (by simp) part rfl)
      (ih rest rfl (fun value hv => hwidth value (by simp [hv]))
        (fun value hv => hdecode value (by simp [hv])))

end milhouse.ssz_items
