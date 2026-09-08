import Tree.Ssz.Bytes

open Aeneas Aeneas.Std Result

namespace ssz.encode

/-- One variable item writes its offset to the output and its payload to the
    temporary vector, retaining the encoder offset and identity write-back. -/
theorem SszEncoder.append_variable_spec {T : Type} (EncodeInst : milhouse.ssz.encode.Encode T)
    (hvariable : EncodeInst.is_ssz_fixed_len = ok false) (self : SszEncoder) (item : T)
    (payload : _root_.List Std.U8)
    (happend : ∃ output, EncodeInst.ssz_append item self.variable_bytes = ok output ∧
      output.val = self.variable_bytes.val ++ payload)
    (hbuf : self.buf.val.length + 4 ≤ Std.Usize.max)
    (hoffset : self.offset.val + self.variable_bytes.val.length ≤ Std.U32.max) :
    ∃ output, SszEncoder.append EncodeInst self item = ok (output, id) ∧
      output.offset = self.offset ∧
      output.buf.val = self.buf.val ++ offsetBytes (self.offset.val + self.variable_bytes.val.length) ∧
      output.variable_bytes.val = self.variable_bytes.val ++ payload := by
  have hword : Std.U32.max ≤ Std.Usize.max := by
    rcases Usize.bounds_eq with h | h <;> simp [h, U32.max_eq, U64.max_eq]
  obtain ⟨offset, hadd, hvalue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := self.offset) (y := self.variable_bytes.len) (by scalar_tac))
  have hvalue' : offset.val = self.offset.val + self.variable_bytes.val.length := by
    simpa using hvalue
  have hlength := encode_length_spec offset (by omega)
  rw [hvalue'] at hlength
  obtain ⟨buf, hbytes, hbytesValue⟩ := append_bytes_spec self.buf
    (offsetBytes (self.offset.val + self.variable_bytes.val.length))
    (by simpa only [offsetBytes_length] using hbuf)
  obtain ⟨variable_bytes, hpayload, hpayloadValue⟩ := happend
  refine ⟨{ self with buf, variable_bytes }, ?_, rfl, hbytesValue, hpayloadValue⟩
  simp only [SszEncoder.append, hvariable, bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
    hadd, hlength, hbytes, hpayload]

/-- Finalization appends the complete variable payload and clears the
    temporary vector while retaining the exact borrowed-buffer continuation. -/
theorem SszEncoder.finalize_spec (self : SszEncoder)
    (hbound : self.buf.val.length + self.variable_bytes.val.length ≤ Std.Usize.max) :
    ∃ output, SszEncoder.finalize self = ok (output,
      (fun replacement => { self with buf := replacement, variable_bytes := alloc.vec.Vec.new Std.U8 }), id) ∧
      output.val = self.buf.val ++ self.variable_bytes.val := by
  obtain ⟨output, happend, houtput⟩ := append_bytes_spec self.buf self.variable_bytes.val hbound
  exact ⟨output, by simp only [SszEncoder.finalize, happend, bind_tc_ok], houtput⟩

end ssz.encode
