import Tree.Ssz.VariableStep

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

private def usizeOfBound (n : Nat) (h : n ≤ Std.Usize.max) : Std.Usize :=
  UScalar.ofNatCore n (by scalar_tac)

/-- The remaining offset-table and payload suffixes determine every cursor
step. All indexing arithmetic is bounded by the input slice itself. -/
private theorem variable_decodes_suffix {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (bytes : Slice Std.U8)
    (originalPayload : _root_.List Std.U8) (first count : Std.Usize)
    (hfirst : first.val = 4 * count.val) (hfirstBound : first.val ≤ bytes.length)
    (values : _root_.List T) (index offset : Std.Usize)
    (hindex : 0 < index.val) (hcount : index.val + values.length = count.val + 1)
    (hoffset : first.val ≤ offset.val) (hoffsetBound : offset.val ≤ bytes.length)
    (htable : bytes.val.drop (4 * (index.val - 1)) =
      _root_.ssz.encode.offsets encode offset.val values ++ originalPayload)
    (hpayload : bytes.val.drop offset.val = values.flatMap encode)
    (hfit : _root_.ssz.encode.OffsetsFit encode offset.val values)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value)) :
    (.Variable bytes first count index offset : SszItems).Decodes decode values none := by
  induction values generalizing index offset with
  | nil =>
    exact .exhausted (SszItems.next_variable_exhausted bytes first count index offset
      (by simp only [_root_.List.length_nil, Nat.add_zero] at hcount; omega))
  | cons value values ih =>
    have hlive : index.val ≤ count.val := by
      simp only [_root_.List.length_cons] at hcount
      omega
    have hsuccessorBound : index.val + 1 ≤ Std.Usize.max := by
      have hb := bytes.property
      simp only [Slice.length] at hfirstBound
      omega
    let successor := usizeOfBound (index.val + 1) hsuccessorBound
    have hsuccessor : successor.val = index.val + 1 := rfl
    have hlength : offset.val + (encode value).length + (values.flatMap encode).length =
        bytes.length := by
      have h := congrArg _root_.List.length hpayload
      simp only [_root_.List.length_drop, _root_.List.flatMap_cons,
        _root_.List.length_append] at h
      simp only [Slice.length] at hoffsetBound ⊢
      omega
    have hpartBound : (encode value).length ≤ Std.Usize.max := by
      have hb := bytes.property
      simp only [Slice.length] at hlength
      omega
    let part : Slice Std.U8 := ⟨encode value, hpartBound⟩
    cases values with
    | nil =>
      have heq : index = count := by
        apply UScalar.eq_of_val_eq
        simpa using hcount
      have hpart : bytes.drop offset = part := by
        apply Subtype.ext
        simpa only [Slice.drop, _root_.List.flatMap_cons, _root_.List.flatMap_nil,
          _root_.List.append_nil] using hpayload
      have hitem := SszItems.variable_item_last bytes first count offset hoffsetBound
      rw [hpart] at hitem
      rw [← heq] at hitem
      exact .cons
        (SszItems.next_variable_step bytes first count index successor offset offset
          (.Ok part) hlive hsuccessor (by simpa only [heq] using hitem))
        (hdecode value (by simp) part rfl)
        (.exhausted (SszItems.next_variable_exhausted bytes first count successor offset
          (by rw [hsuccessor, heq]; omega)))
    | cons nextValue rest =>
      have hnextBound : offset.val + (encode value).length ≤ Std.Usize.max := by
        have hb := bytes.property
        simp only [Slice.length] at hlength
        omega
      let nextOffset := usizeOfBound (offset.val + (encode value).length) hnextBound
      have hnextOffset : nextOffset.val = offset.val + (encode value).length := rfl
      have hpositionBound : 4 * index.val ≤ Std.Usize.max := by
        have hb := bytes.property
        simp only [Slice.length] at hfirstBound
        omega
      let position := usizeOfBound (4 * index.val) hpositionBound
      let tableTail := bytes.drop position
      have htail : tableTail.val = bytes.val.drop (4 * index.val) := rfl
      have htableTail : tableTail.val =
          _root_.ssz.encode.offsets encode nextOffset.val (nextValue :: rest) ++ originalPayload := by
        have h := congrArg (_root_.List.drop 4) htable
        have hdrop (tailBytes : _root_.List Std.U8) :
            _root_.List.drop 4 (_root_.ssz.encode.offsetBytes offset.val ++ tailBytes) =
              tailBytes := by
          rw [← _root_.ssz.encode.offsetBytes_length offset.val, _root_.List.drop_left]
        change _root_.List.drop 4 (bytes.val.drop (4 * (index.val - 1))) =
          _root_.List.drop 4
            ((_root_.ssz.encode.offsetBytes offset.val ++
              _root_.ssz.encode.offsets encode nextOffset.val (nextValue :: rest)) ++
              originalPayload) at h
        rw [_root_.List.drop_drop, _root_.List.append_assoc, hdrop] at h
        have hpos : 4 * (index.val - 1) + 4 = 4 * index.val := by omega
        simpa only [hpos, htail, hnextOffset] using h
      have hnextFit : _root_.ssz.encode.OffsetsFit encode nextOffset.val (nextValue :: rest) :=
        hfit.2
      have hread := _root_.ssz.decode.read_offset_offsetBytes tableTail nextOffset
        (_root_.ssz.encode.offsets encode (nextOffset.val + (encode nextValue).length) rest ++
          originalPayload) hnextFit.1
        (by simpa only [_root_.ssz.encode.offsets, _root_.List.append_assoc] using htableTail)
      have hpart : part.val = bytes.val.slice offset.val nextOffset.val := by
        simp only [_root_.List.slice, hpayload, _root_.List.flatMap_cons, hnextOffset,
          Nat.add_sub_cancel_left, _root_.List.take_left]
        rfl
      have hitem := SszItems.variable_item_between bytes part tableTail first count index
        offset nextOffset (by intro h; subst index; simp only [_root_.List.length_cons] at hcount; omega)
        (by omega) htail hread (by rw [hnextOffset]; omega) (by rw [hnextOffset]; omega)
        (by rw [hnextOffset]; omega) hpart
      apply SszItems.Decodes.cons
        (SszItems.next_variable_step bytes first count index successor offset nextOffset
          (.Ok part) hlive hsuccessor hitem)
        (hdecode value (by simp) part rfl)
      apply ih successor nextOffset (by rw [hsuccessor]; omega)
        (by simp only [_root_.List.length_cons] at hcount ⊢; omega)
        (by rw [hnextOffset]; omega) (by rw [hnextOffset]; omega)
      · have hpos : 4 * (successor.val - 1) = 4 * index.val := by rw [hsuccessor]; omega
        simpa only [hpos, htail] using htableTail
      · have h := congrArg (_root_.List.drop (encode value).length) hpayload
        simpa only [_root_.List.drop_drop, _root_.List.flatMap_cons,
          _root_.List.drop_left, hnextOffset] using h
      · exact hnextFit
      · intro v hv
        exact hdecode v (by simp [hv])

/-- A canonical nonempty variable encoding initializes a cursor which decodes
every represented value in order. The only offset bounds are SSZ's bounds on
the entries actually emitted; no bound on the final payload's end is added. -/
theorem SszItems.variable_decodes_values {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (values : _root_.List T) (bytes : Slice Std.U8)
    (hnonempty : values ≠ [])
    (hbytes : bytes.val = _root_.ssz.encode.variableEncoding encode values)
    (hfit : _root_.ssz.encode.OffsetsFit encode (4 * values.length) values)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value)) :
    ∃ items, SszItems.variable bytes = ok (core.result.Result.Ok items) ∧
      items.Decodes decode values none := by
  have hlength : bytes.length = 4 * values.length + (values.flatMap encode).length := by
    simp only [Slice.length, hbytes, _root_.ssz.encode.variableEncoding_length]
  have hfirstBound : 4 * values.length ≤ Std.Usize.max := by
    have hb := bytes.property
    simp only [Slice.length] at hlength
    omega
  have hcountBound : values.length ≤ Std.Usize.max := by omega
  let first := usizeOfBound (4 * values.length) hfirstBound
  let count := usizeOfBound values.length hcountBound
  have hfirst : first.val = 4 * values.length := rfl
  have hcount : count.val = values.length := rfl
  have hpositive : 0 < count.val := by
    rw [hcount]
    exact _root_.List.length_pos_iff.mpr hnonempty
  have hbound : first.val ≤ bytes.length := by rw [hfirst, hlength]; omega
  have hread : _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok first) := by
    cases values with
    | nil => exact False.elim (hnonempty rfl)
    | cons value rest =>
      exact _root_.ssz.decode.read_offset_offsetBytes bytes first
        (_root_.ssz.encode.offsets encode (first.val + (encode value).length) rest ++
          (value :: rest).flatMap encode) hfit.1
        (by simpa only [_root_.ssz.encode.variableEncoding, _root_.ssz.encode.offsets,
          _root_.List.append_assoc, hfirst] using hbytes)
  refine ⟨.Variable bytes first count 1#usize first,
    SszItems.variable_valid bytes first count hread rfl hpositive hbound, ?_⟩
  apply variable_decodes_suffix decode encode bytes (values.flatMap encode) first count
    rfl hbound values 1#usize first (by decide)
    (by change 1 + values.length = count.val + 1; rw [hcount]; omega) (le_refl _) hbound
  · simpa only [show (1#usize).val = 1 from rfl, Nat.sub_self, Nat.mul_zero,
      _root_.List.drop_zero, hfirst, _root_.ssz.encode.variableEncoding] using hbytes
  · rw [hbytes, _root_.ssz.encode.variableEncoding, hfirst]
    conv_lhs => arg 1; rw [← _root_.ssz.encode.offsets_length encode (4 * values.length) values]
    exact _root_.List.drop_left
  · exact hfit
  · exact hdecode

end milhouse.ssz_items
