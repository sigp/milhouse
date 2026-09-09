import Tree.Ssz.ReadOffset

open Aeneas Aeneas.Std Result

namespace ssz.decode

/-- The first word of a variable prefix is its initial offset, including an
empty prefix. Bounding the final prefix offset suffices for all prefix words. -/
theorem read_offset_prefix {T : Type} (encode : T → List Std.U8)
    (bytes : Slice Std.U8) (first current : Std.Usize) (values : List T) (rest : List Std.U8)
    (hcurrent : current.val = first.val + (values.flatMap encode).length)
    (hfit : current.val ≤ Std.U32.max)
    (hbytes : bytes.val = ssz.encode.offsets encode first.val values ++
      ssz.encode.offsetBytes current.val ++ rest) :
    read_offset bytes = ok (core.result.Result.Ok first) := by
  cases values with
  | nil =>
    have heq : current = first := by
      apply UScalar.eq_of_val_eq
      simpa only [List.flatMap_nil, List.length_nil, Nat.add_zero] using hcurrent
    subst current
    exact read_offset_offsetBytes bytes first rest hfit
      (by simpa only [ssz.encode.offsets, List.nil_append] using hbytes)
  | cons value values =>
    exact read_offset_offsetBytes bytes first
      (ssz.encode.offsets encode (first.val + (encode value).length) values ++
        ssz.encode.offsetBytes current.val ++ rest) (by omega)
      (by simpa only [ssz.encode.offsets, List.append_assoc] using hbytes)

end ssz.decode
