import Tree.Ssz.VariablePrefix
import Tree.Ssz.PrefixRead

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

private def usizeOfBound (n : Nat) (h : n ≤ Std.Usize.max) : Std.Usize :=
  UScalar.ofNatCore n (by scalar_tac)

/-- An invalid nonfinal variable payload stops after exactly its successful
prefix. Its two boundary offsets are checked first; later table entries and
element behavior are unconstrained. Empty invalid payloads are allowed. -/
theorem SszItems.variable_decodes_element_error {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (bytes part : Slice Std.U8)
    (first count current nextOffset : Std.Usize) (values : _root_.List T)
    (tableSuffix payloadSuffix : _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hfirst : first.val = 4 * count.val) (hcount : values.length + 1 < count.val)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hnextFit : nextOffset.val ≤ Std.U32.max) (hnextBound : nextOffset.val ≤ bytes.length)
    (horder : current.val ≤ nextOffset.val)
    (htable : bytes.val = _root_.ssz.encode.offsets encode first.val values ++
      _root_.ssz.encode.offsetBytes current.val ++ _root_.ssz.encode.offsetBytes nextOffset.val ++
        tableSuffix)
    (hpayload : bytes.val.drop first.val = values.flatMap encode ++ payloadSuffix)
    (hdecode : ∀ value ∈ values, ∀ bytes : Slice Std.U8,
      bytes.val = encode value → decode bytes = ok (core.result.Result.Ok value))
    (hpart : part.val = bytes.val.slice current.val nextOffset.val)
    (herror : decode part = ok (core.result.Result.Err error)) :
    (.Variable bytes first count 1#usize first : SszItems).Decodes decode values (some error) := by
  have hfirstBound : first.val ≤ bytes.length := by omega
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
  have htail : tableTail.val = bytes.val.drop (4 * index.val) := rfl
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
  have hitem := SszItems.variable_item_between bytes part tableTail first count index current
    nextOffset hindexNe (by omega) htail hread (by omega) hnextBound horder hpart
  have hend : (.Variable bytes first count index current : SszItems).Decodes decode [] (some error) :=
    .element_error (SszItems.next_variable_step bytes first count index successor current nextOffset
      (.Ok part) (by omega) hsuccessor hitem) herror
  simpa only [_root_.List.append_nil] using SszItems.variable_decodes_prefix decode encode bytes
    first count 1#usize first index current values [] (some error)
    (_root_.ssz.encode.offsetBytes nextOffset.val ++ tableSuffix) payloadSuffix hfirst
    (by decide) (by change 1 + values.length = index.val; omega) (by omega) (le_refl _)
    hfirstBound hcurrent
    (by simpa only [show (1#usize).val = 1 from rfl, Nat.sub_self, Nat.mul_zero,
      _root_.List.drop_zero, _root_.List.append_assoc] using htable)
    hpayload (by omega) hdecode hend

/-- The final variable payload consumes all remaining bytes, possibly none.
Its element error is retained after exactly the preceding successful values.
The complete table supplies the initial offset's input bound internally. -/
theorem SszItems.variable_decodes_final_error {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (encode : T → _root_.List Std.U8) (bytes last : Slice Std.U8)
    (first count current : Std.Usize) (values : _root_.List T)
    (tableSuffix : _root_.List Std.U8) (error : ssz.decode.DecodeError)
    (hfirst : first.val = 4 * count.val) (hcount : values.length + 1 = count.val)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hfit : current.val ≤ Std.U32.max)
    (htable : bytes.val = _root_.ssz.encode.offsets encode first.val values ++
      _root_.ssz.encode.offsetBytes current.val ++ tableSuffix)
    (hpayload : bytes.val.drop first.val = values.flatMap encode ++ last.val)
    (hdecode : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → decode part = ok (core.result.Result.Ok value))
    (herror : decode last = ok (core.result.Result.Err error)) :
    (.Variable bytes first count 1#usize first : SszItems).Decodes decode values (some error) := by
  have hfirstBound : first.val ≤ bytes.length := by
    have hlen := congrArg _root_.List.length htable
    simp only [_root_.List.length_append, _root_.ssz.encode.offsets_length,
      _root_.ssz.encode.offsetBytes_length] at hlen
    simp only [Slice.length]
    omega
  have hcurrentBound : current.val ≤ bytes.length := by
    have hlen := congrArg _root_.List.length hpayload
    simp only [_root_.List.length_drop, _root_.List.length_append] at hlen
    simp only [Slice.length] at hfirstBound ⊢
    omega
  have hlast : bytes.drop current = last := by
    apply Subtype.ext
    have h := congrArg (_root_.List.drop (values.flatMap encode).length) hpayload
    simpa only [_root_.List.drop_drop, _root_.List.drop_left, Slice.drop, hcurrent] using h
  have hsuccessorBound : count.val + 1 ≤ Std.Usize.max := by
    have hb := bytes.property
    simp only [Slice.length] at hfirstBound
    omega
  let successor := usizeOfBound (count.val + 1) hsuccessorBound
  have hsuccessor : successor.val = count.val + 1 := rfl
  have hitem := SszItems.variable_item_last bytes first count current hcurrentBound
  rw [hlast] at hitem
  have hend : (.Variable bytes first count count current : SszItems).Decodes decode [] (some error) :=
    .element_error (SszItems.next_variable_step bytes first count count successor current current
      (.Ok last) (le_refl _) hsuccessor hitem) herror
  simpa only [_root_.List.append_nil] using SszItems.variable_decodes_prefix decode encode bytes
    first count 1#usize first count current values [] (some error) tableSuffix last.val hfirst
    (by decide) (by change 1 + values.length = count.val; omega) (le_refl _) (le_refl _)
    hfirstBound hcurrent
    (by simpa only [show (1#usize).val = 1 from rfl, Nat.sub_self, Nat.mul_zero,
      _root_.List.drop_zero] using htable) hpayload hfit hdecode hend

end milhouse.ssz_items
