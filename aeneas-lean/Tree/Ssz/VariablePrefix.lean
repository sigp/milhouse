import Tree.Ssz.VariableStep

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

private def usizeOfBound (n : Nat) (h : n ≤ Std.Usize.max) : Std.Usize :=
  UScalar.ofNatCore n (by scalar_tac)

/-- Complete variable payloads and their table entries can be prepended to
any remaining cursor behavior. The remaining table and payload bytes are
unconstrained. The prefix ends at a real table entry, so every prepended item
uses its next offset; the final item, exhaustion, or error belongs to `htail`.
Only the largest consumed offset needs an explicit 32-bit bound. -/
theorem SszItems.variable_decodes_prefix {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (bytes : Slice Std.U8)
    (first count index offset finalIndex finalOffset : Std.Usize)
    (values suffixValues : _root_.List T) (error : Option ssz.decode.DecodeError)
    (tableSuffix payloadSuffix : _root_.List Std.U8)
    (hfirst : first.val = 4 * count.val)
    (hindex : 0 < index.val) (hfinalIndex : index.val + values.length = finalIndex.val)
    (hcount : finalIndex.val ≤ count.val)
    (hoffset : first.val ≤ offset.val) (hoffsetBound : offset.val ≤ bytes.length)
    (hfinalOffset : finalOffset.val = offset.val + (values.flatMap encode).length)
    (htable : bytes.val.drop (4 * (index.val - 1)) =
      _root_.ssz.encode.offsets encode offset.val values ++
        _root_.ssz.encode.offsetBytes finalOffset.val ++ tableSuffix)
    (hpayload : bytes.val.drop offset.val = values.flatMap encode ++ payloadSuffix)
    (hfit : finalOffset.val ≤ Std.U32.max)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value))
    (htail : (.Variable bytes first count finalIndex finalOffset : SszItems).Decodes
      decode suffixValues error) :
    (.Variable bytes first count index offset : SszItems).Decodes
      decode (values ++ suffixValues) error := by
  induction values generalizing index offset with
  | nil =>
    have hi : index = finalIndex := by
      apply UScalar.eq_of_val_eq
      simpa only [_root_.List.length_nil, Nat.add_zero] using hfinalIndex
    have ho : offset = finalOffset := by
      apply UScalar.eq_of_val_eq
      simpa only [_root_.List.flatMap_nil, _root_.List.length_nil, Nat.add_zero] using
        hfinalOffset.symm
    simpa only [hi, ho, _root_.List.nil_append] using htail
  | cons value values ih =>
    have hlive : index.val < count.val := by
      simp only [_root_.List.length_cons] at hfinalIndex
      omega
    have hsuccessorBound : index.val + 1 ≤ Std.Usize.max := by
      have hb := bytes.property
      simp only [Slice.length] at hoffsetBound
      omega
    let successor := usizeOfBound (index.val + 1) hsuccessorBound
    have hsuccessor : successor.val = index.val + 1 := rfl
    have hlength : offset.val + (encode value).length +
        (values.flatMap encode).length + payloadSuffix.length = bytes.length := by
      have h := congrArg _root_.List.length hpayload
      simp only [_root_.List.length_drop, _root_.List.flatMap_cons,
        _root_.List.length_append] at h
      simp only [Slice.length] at hoffsetBound ⊢
      omega
    have hnextBound : offset.val + (encode value).length ≤ Std.Usize.max := by
      have hb := bytes.property
      simp only [Slice.length] at hlength
      omega
    let nextOffset := usizeOfBound (offset.val + (encode value).length) hnextBound
    have hnextOffset : nextOffset.val = offset.val + (encode value).length := rfl
    have hpartBound : (encode value).length ≤ Std.Usize.max := by omega
    let part : Slice Std.U8 := ⟨encode value, hpartBound⟩
    have hpositionBound : 4 * index.val ≤ Std.Usize.max := by
      have hb := bytes.property
      simp only [Slice.length] at hoffsetBound
      omega
    let position := usizeOfBound (4 * index.val) hpositionBound
    let tableTail := bytes.drop position
    have htableTailVal : tableTail.val = bytes.val.drop (4 * index.val) := rfl
    have htableTail : tableTail.val =
        _root_.ssz.encode.offsets encode nextOffset.val values ++
          _root_.ssz.encode.offsetBytes finalOffset.val ++ tableSuffix := by
      have h := congrArg (_root_.List.drop 4) htable
      have hdrop (tailBytes : _root_.List Std.U8) :
          _root_.List.drop 4 (_root_.ssz.encode.offsetBytes offset.val ++ tailBytes) =
            tailBytes := by
        rw [← _root_.ssz.encode.offsetBytes_length offset.val, _root_.List.drop_left]
      simp only [_root_.ssz.encode.offsets, _root_.List.append_assoc] at h
      rw [_root_.List.drop_drop, hdrop] at h
      have hpos : 4 * (index.val - 1) + 4 = 4 * index.val := by omega
      simpa only [hpos, htableTailVal, hnextOffset, _root_.List.append_assoc] using h
    have hread : _root_.ssz.decode.read_offset tableTail = ok (core.result.Result.Ok nextOffset) := by
      cases values with
      | nil =>
        have heq : nextOffset = finalOffset := by
          apply UScalar.eq_of_val_eq
          simp only [_root_.List.flatMap_cons, _root_.List.flatMap_nil,
            _root_.List.append_nil] at hfinalOffset
          omega
        subst finalOffset
        exact _root_.ssz.decode.read_offset_offsetBytes tableTail nextOffset tableSuffix hfit
          (by simpa only [_root_.ssz.encode.offsets, _root_.List.nil_append] using htableTail)
      | cons nextValue rest =>
        apply _root_.ssz.decode.read_offset_offsetBytes tableTail nextOffset
          (_root_.ssz.encode.offsets encode (nextOffset.val + (encode nextValue).length) rest ++
            _root_.ssz.encode.offsetBytes finalOffset.val ++ tableSuffix)
        · simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hfinalOffset
          omega
        · simpa only [_root_.ssz.encode.offsets, _root_.List.append_assoc] using htableTail
    have hpart : part.val = bytes.val.slice offset.val nextOffset.val := by
      simp only [_root_.List.slice, hpayload, _root_.List.flatMap_cons, hnextOffset,
        Nat.add_sub_cancel_left, _root_.List.append_assoc, _root_.List.take_left]
      rfl
    have hitem := SszItems.variable_item_between bytes part tableTail first count index offset
      nextOffset (by intro h; subst index; omega) (by omega) rfl hread
      (by omega) (by omega) (by omega) hpart
    apply SszItems.Decodes.cons
      (SszItems.next_variable_step bytes first count index successor offset nextOffset (.Ok part)
        (by omega) hsuccessor hitem) (hdecode value (by simp) part rfl)
    apply ih successor nextOffset (by omega)
      (by simp only [_root_.List.length_cons] at hfinalIndex; omega) (by omega) (by omega)
    · simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hfinalOffset
      omega
    · have hpos : 4 * (successor.val - 1) = 4 * index.val := by omega
      simpa only [hpos, htableTailVal] using htableTail
    · have h := congrArg (_root_.List.drop (encode value).length) hpayload
      simpa only [_root_.List.drop_drop, _root_.List.flatMap_cons,
        _root_.List.append_assoc, _root_.List.drop_left, hnextOffset] using h
    · intro v hv
      exact hdecode v (by simp [hv])

end milhouse.ssz_items
