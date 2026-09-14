import Tree.Formatting.Models

open Aeneas Aeneas.Std Result

namespace milhouse_fmt

private theorem byteArray_toList (bytes : ByteArray) :
    bytes.toList = bytes.data.toList := by
  have loop (i : Nat) (acc : List UInt8) (hi : i ≤ bytes.size) :
      ByteArray.toList.loop bytes i acc = acc.reverse ++ bytes.data.toList.drop i := by
    fun_induction ByteArray.toList.loop bytes i acc with
    | case1 i acc h ih =>
      rw [ih (by omega)]
      have hd : i < bytes.data.toList.length := by simpa using h
      rw [List.drop_eq_getElem_cons hd]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.append_cancel_left_eq, List.cons.injEq, and_true, ByteArray.get!,
        _root_.Array.getElem_toList]
      exact getElem!_pos bytes.data i (by simpa using h)
    | case2 i acc h =>
      have heq : i = bytes.size := by omega
      simp [heq]
  simpa [ByteArray.toList] using loop 0 [] (by omega)

theorem utf8_toStr (s : String) (h : s.toByteArray.size ≤ Std.U32.max) :
    utf8 (toStr s h).val = ok s := by
  simp only [utf8, toStr, Slice.from_val, List.map_map, byteArray_toList]
  change (match String.fromUTF8?
      ⟨(s.toByteArray.data.toList.map fun x => UInt8.ofNat x.toNat).toArray⟩ with
      | some output => ok output
      | none => fail .panic) = ok s
  simp only [UInt8.ofNat_toNat]
  have hid : _root_.List.map (fun x : UInt8 => x) s.toByteArray.data.toList =
      s.toByteArray.data.toList := _root_.List.map_id _
  rw [hid]
  change (match String.fromUTF8? s.toByteArray with
    | some output => ok output | none => fail .panic) = ok s
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

end milhouse_fmt
