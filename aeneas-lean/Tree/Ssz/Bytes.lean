import Tree.Ssz.Models

open Aeneas Aeneas.Std Result

namespace ssz.encode

/-- The canonical four-byte little-endian representation of an SSZ offset. -/
def offsetBytes (offset : Nat) : _root_.List Std.U8 :=
  (BitVec.ofNat 32 offset).toLEBytes.map (@UScalar.mk .U8)

theorem offsetBytes_length (offset : Nat) : (offsetBytes offset).length = 4 := by
  simp [offsetBytes, BitVec.toLEBytes_length]

theorem encode_length_spec (offset : Std.Usize) (hbound : offset.val ≤ Std.U32.max) :
    encode_length offset = ok (offsetBytes offset.val) := by
  simp only [encode_length, hbound, ↓reduceIte, offsetBytes,
    core.num.U32.to_le_bytes, UScalar.cast]
  congr 3
  exact (BitVec.ofNat_toNat 32 offset.bv).symm

theorem append_bytes_spec (buf : alloc.vec.Vec Std.U8) (bytes : _root_.List Std.U8)
    (hbound : buf.val.length + bytes.length ≤ Std.Usize.max) :
    ∃ output, append_bytes buf bytes = ok output ∧ output.val = buf.val ++ bytes := by
  exact ⟨⟨buf.val ++ bytes, by simpa only [_root_.List.length_append] using hbound⟩,
    by simp [append_bytes, hbound], rfl⟩

/-- Offsets for variable items, starting at the fixed section's size and
    advancing by the exact encoded payload size of each preceding item. -/
def offsets {T : Type} (encode : T → _root_.List Std.U8) : Nat → _root_.List T → _root_.List Std.U8
  | _, [] => []
  | offset, value :: values => offsetBytes offset ++ offsets encode (offset + (encode value).length) values

theorem offsets_length {T : Type} (encode : T → _root_.List Std.U8)
    (offset : Nat) (values : _root_.List T) : (offsets encode offset values).length = 4 * values.length := by
  induction values generalizing offset with
  | nil => simp [offsets]
  | cons value values ih =>
    simp [offsets, offsetBytes_length, ih, Nat.mul_add, Nat.add_comm]

/-- Only the offsets actually written must fit 32 bits. In particular, this
    imposes no unnecessary 32-bit bound on the end of the final payload. -/
def OffsetsFit {T : Type} (encode : T → _root_.List Std.U8) : Nat → _root_.List T → Prop
  | _, [] => True
  | offset, value :: values => offset ≤ Std.U32.max ∧ OffsetsFit encode (offset + (encode value).length) values

def variableEncoding {T : Type} (encode : T → _root_.List Std.U8) (values : _root_.List T) :
    _root_.List Std.U8 := offsets encode (4 * values.length) values ++ values.flatMap encode

theorem variableEncoding_length {T : Type} (encode : T → _root_.List Std.U8) (values : _root_.List T) :
    (variableEncoding encode values).length = 4 * values.length + (values.flatMap encode).length := by
  simp only [variableEncoding, _root_.List.length_append, offsets_length]

end ssz.encode
