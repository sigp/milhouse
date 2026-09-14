import Tree.Ssz.VariablePrefix
import Tree.Ssz.VariableErrors
import Tree.Ssz.PrefixRead

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

private def usizeOfBound (n : Nat) (h : n ≤ Std.Usize.max) : Std.Usize :=
  UScalar.ofNatCore n (by scalar_tac)

/-- After any complete variable prefix, a malformed next offset stops before
decoding the following payload. The result respects fixed-section, bounds,
then decreasing-offset precedence. All cursor steps are derived from the raw
table and prefix payload bytes; only successfully consumed values need laws. -/
theorem SszItems.variable_decodes_offset_error {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (bytes : Slice Std.U8)
    (first count current nextOffset : Std.Usize) (values : _root_.List T)
    (tableSuffix payloadSuffix : _root_.List Std.U8)
    (hfirst : first.val = 4 * count.val) (hcount : values.length + 1 < count.val)
    (hfirstBound : first.val ≤ bytes.length)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hcurrentFit : current.val ≤ Std.U32.max) (hnextFit : nextOffset.val ≤ Std.U32.max)
    (htable : bytes.val = _root_.ssz.encode.offsets encode first.val values ++
      _root_.ssz.encode.offsetBytes current.val ++ _root_.ssz.encode.offsetBytes nextOffset.val ++
        tableSuffix)
    (hpayload : bytes.val.drop first.val = values.flatMap encode ++ payloadSuffix)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value))
    (hbad : nextOffset.val < first.val ∨ bytes.length < nextOffset.val ∨
      nextOffset.val < current.val) :
    let error := if nextOffset.val < first.val then
        ssz.decode.DecodeError.OffsetIntoFixedPortion nextOffset
      else if bytes.length < nextOffset.val then ssz.decode.DecodeError.OffsetOutOfBounds nextOffset
      else ssz.decode.DecodeError.OffsetsAreDecreasing nextOffset
    (.Variable bytes first count 1#usize first : SszItems).Decodes decode values (some error) := by
  let error := if nextOffset.val < first.val then
      ssz.decode.DecodeError.OffsetIntoFixedPortion nextOffset
    else if bytes.length < nextOffset.val then ssz.decode.DecodeError.OffsetOutOfBounds nextOffset
    else ssz.decode.DecodeError.OffsetsAreDecreasing nextOffset
  change (.Variable bytes first count 1#usize first : SszItems).Decodes decode values (some error)
  have hindexBound : values.length + 1 ≤ Std.Usize.max := by
    have hb : count.val ≤ Std.Usize.max := by scalar_tac
    omega
  let index := usizeOfBound (values.length + 1) hindexBound
  have hindex : index.val = values.length + 1 := rfl
  have hsuccessorBound : index.val + 1 ≤ Std.Usize.max := by
    have hb : count.val ≤ Std.Usize.max := by scalar_tac
    omega
  let successor := usizeOfBound (index.val + 1) hsuccessorBound
  have hsuccessor : successor.val = index.val + 1 := rfl
  have hpositionBound : 4 * index.val ≤ Std.Usize.max := by
    have hb := bytes.property
    simp only [Slice.length] at hfirstBound
    omega
  let position := usizeOfBound (4 * index.val) hpositionBound
  let tableTail := bytes.drop position
  have htail : tableTail.val = bytes.val.drop (4 * index.val) := by
    simp [tableTail, Slice.drop, position, usizeOfBound]
  have htableTail : tableTail.val = _root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix := by
    have hlen : (_root_.ssz.encode.offsets encode first.val values ++
        _root_.ssz.encode.offsetBytes current.val).length = 4 * index.val := by
      simp only [_root_.List.length_append, _root_.ssz.encode.offsets_length,
        _root_.ssz.encode.offsetBytes_length, hindex]
      omega
    rw [htail, htable, _root_.List.append_assoc
      (_root_.ssz.encode.offsets encode first.val values ++
        _root_.ssz.encode.offsetBytes current.val), ← hlen, _root_.List.drop_left]
  have hread := _root_.ssz.decode.read_offset_offsetBytes tableTail nextOffset tableSuffix
    hnextFit htableTail
  have hindexNe : index ≠ count := by
    intro h
    have hv := congrArg UScalar.val h
    omega
  have htableBound : 4 * index.val ≤ bytes.length := by omega
  have hitem : SszItems.variable_item bytes first count index current =
      ok (core.result.Result.Err error, current) := by
    by_cases hfixed : nextOffset.val < first.val
    · simpa only [error, hfixed, ↓reduceIte] using SszItems.variable_item_into_fixed bytes tableTail
        first count index current nextOffset hindexNe htableBound htail hread hfixed
    · by_cases hbound : bytes.length < nextOffset.val
      · simpa only [error, hfixed, hbound, ↓reduceIte] using
          SszItems.variable_item_out_of_bounds bytes tableTail first count index current nextOffset
            hindexNe htableBound htail hread (by omega) hbound
      · simpa only [error, hfixed, hbound, ↓reduceIte] using
          SszItems.variable_item_decreasing bytes tableTail first count index current nextOffset
            hindexNe htableBound htail hread (by omega) (by omega) (by omega)
  have hend : (.Variable bytes first count index current : SszItems).Decodes decode [] (some error) :=
    .boundary_error (SszItems.next_variable_step bytes first count index successor current current
      (.Err error) (by omega) hsuccessor hitem)
  simpa only [_root_.List.append_nil] using SszItems.variable_decodes_prefix decode encode bytes
    first count 1#usize first index current values [] (some error)
    (_root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix) payloadSuffix hfirst
    (by decide) (by change 1 + values.length = index.val; omega) (by omega) (le_refl _)
    hfirstBound hcurrent
    (by simpa only [show (1#usize).val = 1 from rfl, Nat.sub_self, Nat.mul_zero,
      _root_.List.drop_zero, _root_.List.append_assoc] using htable)
    hpayload hcurrentFit hdecode hend

end milhouse.ssz_items
