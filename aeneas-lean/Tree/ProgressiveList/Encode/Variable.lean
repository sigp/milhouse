import Tree.ProgressiveList.Encode.VariableLoop

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree
open _root_.ssz.encode

namespace milhouse.progressive_list

/-- Variable-element SSZ writes one offset per represented element followed
    by the exact payload sequence, including pending replacements/extensions.
    The destination prefix is preserved. Only actual offsets need to fit
    32 bits; the final output bound supplies all allocation/arithmetic bounds.
    Element laws apply only to the accumulated temporary payload, independent
    of the destination prefix and offset table. -/
theorem ProgressiveList.ssz_append_variable_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (encode : T → _root_.List Std.U8) (buf : alloc.vec.Vec Std.U8)
    (happend : ∀ before value after, contents = before ++ value :: after →
      ∀ buffer : alloc.vec.Vec Std.U8, buffer.val = before.flatMap encode →
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hbound : buf.val.length + 4 * contents.length + (contents.flatMap encode).length ≤ Std.Usize.max)
    (hoffsets : OffsetsFit encode (4 * contents.length) contents) :
    ∃ output, ProgressiveList.Insts.SszEncodeEncode.ssz_append ValueInst mapInst self buf = ok output ∧
      output.val = buf.val ++ variableEncoding encode contents := by
  obtain ⟨cursor, hiter, _, _, hyields⟩ :=
    ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  obtain ⟨count, hcount, hcountValue⟩ := hrep.1
  obtain ⟨fixed, hmul, hfixed⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := count) (y := 4#usize) (by simp [hcountValue]; omega))
  have hfixedValue : fixed.val = 4 * contents.length := by
    simpa [hcountValue, Nat.mul_comm] using hfixed
  have hreserve : alloc.vec.Vec.reserve Global buf fixed = ok buf := by
    simp only [alloc.vec.Vec.reserve, hfixedValue]
    split
    · rfl
    · omega
  let encoder : SszEncoder := ⟨fixed, buf, alloc.vec.Vec.new Std.U8⟩
  have hcontainer : SszEncoder.container buf fixed = ok (encoder, fun se => se.buf) := by
    simp only [SszEncoder.container, hreserve, bind_tc_ok, encoder]
  obtain ⟨encoded, hloop, _, hencodedBuf, hencodedPayload⟩ :=
    ProgressiveList.ssz_append_variable_loop_spec ValueInst mapInst hvariable cursor contents
      encode encoder id hyields happend
      (by dsimp [encoder]; omega)
    (by simp only [encoder, alloc.vec.Vec.new, alloc.vec.Vec.from_val, _root_.List.length_nil, Nat.zero_add]; omega)
      (by simpa [encoder, hfixedValue] using hoffsets)
  have hfinalBound : encoded.buf.val.length + encoded.variable_bytes.val.length ≤ Std.Usize.max := by
    simpa [hencodedBuf, hencodedPayload, encoder, offsets_length] using hbound
  obtain ⟨output, hfinal, houtput⟩ := SszEncoder.finalize_spec encoded hfinalBound
  have hloop' : ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1
      ValueInst mapInst (fun se => se) encoder cursor = ok (encoded, fun se => se) := hloop
  refine ⟨output, ?_, ?_⟩
  · simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append, hvariable,
      bind_tc_ok, Bool.false_eq_true, ↓reduceIte, hcount, ssz.BYTES_PER_LENGTH_OFFSET,
      hmul, hcontainer, hiter, hloop', hfinal, id_eq]
  · simpa [hencodedBuf, hencodedPayload, encoder, hfixedValue, variableEncoding,
      _root_.List.append_assoc] using houtput

end milhouse.progressive_list
