import Tree.Ssz.DecodeModels
import Tree.Ssz.Bytes

open Aeneas Aeneas.Std Result

namespace ssz.decode

theorem read_offset_short (bytes : Slice Std.U8) (hshort : bytes.val.length < 4) :
    read_offset bytes = ok (core.result.Result.Err
      (milhouse.ssz.decode.DecodeError.InvalidLengthPrefix bytes.len 4#usize)) := by
  unfold read_offset
  split
  · simp_all; omega
  · rfl

/-- Reading is insensitive to bytes beyond the four-byte prefix. -/
theorem read_offset_four (bytes : Slice Std.U8) (a b c d : Std.U8) (rest : List Std.U8)
    (hbytes : bytes.val = a :: b :: c :: d :: rest) :
    read_offset bytes = ok (core.result.Result.Ok
      (UScalar.cast .Usize (core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d])))) := by
  simp [read_offset, hbytes]

private theorem u32_from_to_le (offset : Std.U32) :
    core.num.U32.from_le_bytes (core.num.U32.to_le_bytes offset) = offset := by
  apply UScalar.eq_of_val_eq
  simp only [core.num.U32.from_le_bytes, core.num.U32.to_le_bytes,
    UScalar.val, BitVec.toNat_cast]
  have hmap : _root_.List.map U8.bv (_root_.List.map (@UScalar.mk .U8) offset.bv.toLEBytes) =
      offset.bv.toLEBytes := by
    rw [_root_.List.map_map]
    exact _root_.List.map_id _
  rw [hmap, BitVec.fromLEBytes_toLEBytes (by decide)]
  rfl

theorem read_offset_array (bytes : Slice Std.U8) (word : Array Std.U8 4#usize)
    (rest : List Std.U8) (hbytes : bytes.val = word.val ++ rest) :
    read_offset bytes = ok (core.result.Result.Ok
      (UScalar.cast .Usize (core.num.U32.from_le_bytes word))) := by
  have hlen : word.val.length = 4 := word.property
  obtain ⟨a, b, c, d, hword⟩ := List.length_eq_four.mp hlen
  have hw : word = Array.make 4#usize [a, b, c, d] := by
    apply Subtype.ext
    exact hword
  subst word
  exact read_offset_four bytes a b c d rest hbytes

/-- Canonical little-endian offset bytes decode back to the original 32-bit
word on either supported usize width, with an arbitrary following payload. -/
theorem read_offset_to_le (bytes : Slice Std.U8) (offset : Std.U32)
    (rest : List Std.U8)
    (hbytes : bytes.val = (core.num.U32.to_le_bytes offset).val ++ rest) :
    read_offset bytes = ok (core.result.Result.Ok (UScalar.cast .Usize offset)) := by
  simpa only [u32_from_to_le] using
    read_offset_array bytes (core.num.U32.to_le_bytes offset) rest hbytes

end ssz.decode
