import Tree.ProgressiveList.Iter.Construction
import Tree.Ssz.Encoder

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree
open _root_.ssz.encode

namespace milhouse.progressive_list

/-- Streaming variable encoding writes the complete offset table and payload
    in order, while composing no change into the borrowed-buffer continuation.
    Only emitted offsets must fit 32 bits, and aggregate vector bounds supply
    every intermediate append bound. Element laws concern only the temporary
    payload buffer at each actual sequence position. -/
theorem ProgressiveList.ssz_append_variable_loop_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    (cursor : ProgressiveListIter T U) (values : _root_.List T)
    (encode : T → _root_.List Std.U8) (encoder : SszEncoder) (back : SszEncoder → SszEncoder)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) cursor values)
    (happend : ∀ before value after, values = before ++ value :: after →
      ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val = encoder.variable_bytes.val ++ before.flatMap encode →
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hbuf : encoder.buf.val.length + 4 * values.length ≤ Std.Usize.max)
    (hpayload : encoder.variable_bytes.val.length + (values.flatMap encode).length ≤ Std.Usize.max)
    (hoffsets : OffsetsFit encode (encoder.offset.val + encoder.variable_bytes.val.length) values) :
    ∃ output, ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1
      ValueInst mapInst back encoder cursor = ok (output, back) ∧
      output.offset = encoder.offset ∧
      output.buf.val = encoder.buf.val ++ offsets encode
        (encoder.offset.val + encoder.variable_bytes.val.length) values ∧
      output.variable_bytes.val = encoder.variable_bytes.val ++ values.flatMap encode := by
  induction hyields generalizing encoder with
  | nil hnext =>
    refine ⟨encoder, ?_, rfl, by simp [offsets], by simp⟩
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1.body, hnext, bind_tc_ok]
  | @cons cursor rest value values hnext hyields ih =>
    have hroom : encoder.variable_bytes.val.length + (encode value).length ≤ Std.Usize.max := by
      simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hpayload
      omega
    have hbufRoom : encoder.buf.val.length + 4 ≤ Std.Usize.max := by
      simp only [_root_.List.length_cons, Nat.mul_add, Nat.mul_one] at hbuf
      omega
    obtain ⟨appended, hitem, hitemOffset, hitemBuf, hitemPayload⟩ :=
      SszEncoder.append_variable_spec ValueInst.sszencodeEncodeInst hvariable encoder value
        (encode value) (happend [] value values rfl encoder.variable_bytes (by simp) hroom)
        hbufRoom hoffsets.1
    have htailBuf : appended.buf.val.length + 4 * values.length ≤ Std.Usize.max := by
      rw [hitemBuf, _root_.List.length_append, offsetBytes_length]
      simp only [_root_.List.length_cons, Nat.mul_add, Nat.mul_one] at hbuf
      omega
    have htailPayload : appended.variable_bytes.val.length + (values.flatMap encode).length ≤ Std.Usize.max := by
      rw [hitemPayload, _root_.List.length_append]
      simp only [_root_.List.flatMap_cons, _root_.List.length_append] at hpayload
      omega
    have htailOffsets : OffsetsFit encode (appended.offset.val + appended.variable_bytes.val.length) values := by
      simpa only [hitemOffset, hitemPayload, _root_.List.length_append, Nat.add_assoc] using hoffsets.2
    obtain ⟨output, hloop, houtputOffset, houtputBuf, houtputPayload⟩ := ih appended (by
      intro before item after hsplit buffer hbuffer hroom
      apply happend (value :: before) item after (by simp [hsplit]) buffer ?_ hroom
      simpa only [hitemPayload, _root_.List.flatMap_cons, _root_.List.append_assoc] using hbuffer)
      htailBuf htailPayload htailOffsets
    refine ⟨output, ?_, houtputOffset.trans hitemOffset, ?_, ?_⟩
    · rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1, loop]
      simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1.body,
        hnext, bind_tc_ok, hitem, id_eq]
      exact hloop
    · simpa only [hitemBuf, hitemOffset, hitemPayload, _root_.List.length_append,
        offsets, _root_.List.append_assoc, Nat.add_assoc] using houtputBuf
    · simpa only [hitemPayload, _root_.List.flatMap_cons, _root_.List.append_assoc] using houtputPayload

end milhouse.progressive_list
