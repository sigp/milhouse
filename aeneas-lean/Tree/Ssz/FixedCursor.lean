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
    change ok (core.cmp.impls.OrdUsize.min width bytes.len) = ok width
    congr 1
    apply UScalar.eq_of_val_eq
    simpa only [core.cmp.impls.OrdUsize.min_val, Slice.len_val] using Nat.min_eq_left hbound
  have hsplit : core.slice.Slice.split_at bytes width = ok (part, rest) := by
    simp only [core.slice.Slice.split_at, hbound, ↓reduceDIte, _root_.List.splitAt_eq]
    congr 1
    apply Prod.ext <;> apply Slice.ext
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
      ok (some (core.result.Result.Ok bytes), .Fixed (Slice.from [] (by simp)) width) := by
  have hmin : core.cmp.min core.cmp.OrdUsize width bytes.len = ok bytes.len := by
    change ok (core.cmp.impls.OrdUsize.min width bytes.len) = ok bytes.len
    congr 1
    apply UScalar.eq_of_val_eq
    simpa only [core.cmp.impls.OrdUsize.min_val, Slice.len_val] using Nat.min_eq_right hshort
  have hsplit : core.slice.Slice.split_at bytes bytes.len =
      ok (bytes, Slice.from [] (by simp)) := by
    simp only [core.slice.Slice.split_at, Slice.len_val, le_refl, ↓reduceDIte,
      _root_.List.splitAt_eq]
    congr 1
    apply Prod.ext <;> apply Slice.ext <;> simp [Slice.length]
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
    let part : Slice Std.U8 := Slice.from (encode value) hpartBound
    let rest : Slice Std.U8 := Slice.from (values.flatMap encode) hrestBound
    exact .cons
      (SszItems.next_fixed_full bytes part rest width (by simpa [part, rest] using hbytes)
        (by simpa [part] using hhead) hpositive)
      (hdecode value (by simp) part (by simp [part]))
      (ih rest (by simp [rest]) (fun value hv => hwidth value (by simp [hv]))
        (fun value hv => hdecode value (by simp [hv])))

end milhouse.ssz_items
