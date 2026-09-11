import Tree.Ssz.Models
import Tree.Ssz.DecodeModels
import SszSource.Funs
open Aeneas Aeneas.Std Result

theorem width_agrees : ok SszSource.ssz.BYTES_PER_LENGTH_OFFSET = ssz.BYTES_PER_LENGTH_OFFSET := by
  simp [SszSource.ssz.BYTES_PER_LENGTH_OFFSET, ssz.BYTES_PER_LENGTH_OFFSET]

private theorem usize_add_eq {x y z : Usize} (h : x.val + y.val = z.val) :
    x + y = ok z := by
  obtain ⟨result, hrun, hval⟩ := WP.spec_imp_exists
    (@UScalar.add_spec .Usize x y (by scalar_tac))
  have heq : result = z := UScalar.eq_of_val_eq (by omega)
  simpa [heq] using hrun

private theorem source_decode_four (a b c d : U8) :
    SszSource.ssz.decode.decode_offset (Array.make 4#usize [a,b,c,d]).to_slice =
      ok (.Ok (UScalar.cast .Usize (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])))) := by
  have h01 := usize_add_eq (x := 0#usize) (y := 1#usize) (z := 1#usize) (by scalar_tac)
  have h12 := usize_add_eq (x := 1#usize) (y := 1#usize) (z := 2#usize) (by scalar_tac)
  have h23 := usize_add_eq (x := 2#usize) (y := 1#usize) (z := 3#usize) (by scalar_tac)
  have h34 := usize_add_eq (x := 3#usize) (y := 1#usize) (z := 4#usize) (by scalar_tac)
  simp only [SszSource.ssz.decode.decode_offset, SszSource.ssz.BYTES_PER_LENGTH_OFFSET]
  simp [core.default.DefaultArray.default,
    SszSource.core.slice.Slice.clone_from_slice,
    SszSource.Slice.Insts.CoreSliceCloneFromSpec.spec_clone_from,
    SszSource.Slice.Insts.CoreSliceCloneFromSpec.spec_clone_from_loop,
    Array.to_slice_mut, Array.to_slice, Array.repeat, Array.make, lift,
    core.slice.index.SliceIndexRangeToUsizeSlice.index, Slice.len]
  iterate 5
    rw [loop]
    simp [SszSource.Slice.Insts.CoreSliceCloneFromSpec.spec_clone_from_loop.body,
      Slice.len, Slice.index_mut_usize, Slice.index_usize, Slice.set, Slice.setAtNat,
      h01, h12, h23, h34, Array.from_slice]

private def errorToModel : SszSource.ssz.decode.SourceDecodeError → milhouse.ssz.decode.DecodeError
  | .InvalidByteLength len expected => .InvalidByteLength len expected
  | .InvalidLengthPrefix len expected => .InvalidLengthPrefix len expected
  | .OutOfBoundsByte index => .OutOfBoundsByte index
  | .OffsetIntoFixedPortion offset => .OffsetIntoFixedPortion offset
  | .OffsetSkipsVariableBytes offset => .OffsetSkipsVariableBytes offset
  | .OffsetsAreDecreasing offset => .OffsetsAreDecreasing offset
  | .OffsetOutOfBounds offset => .OffsetOutOfBounds offset
  | .InvalidListFixedBytesLen length => .InvalidListFixedBytesLen length
  | .ZeroLengthItem => .ZeroLengthItem
  | .BytesInvalid message => .BytesInvalid message
  | .UnionSelectorInvalid selector => .UnionSelectorInvalid selector
  | .NoMatchingVariant => .NoMatchingVariant

private def resultToModel :
    core.result.Result Usize SszSource.ssz.decode.SourceDecodeError →
      core.result.Result Usize milhouse.ssz.decode.DecodeError
  | .Ok value => .Ok value
  | .Err error => .Err (errorToModel error)

private theorem source_decode_wrong_length (bytes : Slice U8) (hlen : bytes.val.length ≠ 4) :
    SszSource.ssz.decode.decode_offset bytes =
      ok (.Err (.InvalidLengthPrefix bytes.len 4#usize)) := by
  have hne : bytes.len ≠ 4#usize := by
    intro h
    apply hlen
    simpa using congrArg UScalar.val h
  simp [SszSource.ssz.decode.decode_offset, SszSource.ssz.BYTES_PER_LENGTH_OFFSET, hne]

theorem decode_offset_agrees (bytes : Slice U8) :
    (do let value ← SszSource.ssz.decode.decode_offset bytes; ok (resultToModel value)) =
      if bytes.val.length = 4 then ssz.decode.read_offset bytes
      else ok (.Err (.InvalidLengthPrefix bytes.len 4#usize)) := by
  by_cases hlen : bytes.val.length = 4
  · have hform : ∃ a b c d, bytes = (Array.make 4#usize [a,b,c,d]).to_slice := by
      refine ⟨bytes.val[0]'(by omega), bytes.val[1]'(by omega),
        bytes.val[2]'(by omega), bytes.val[3]'(by omega), ?_⟩
      apply Slice.ext
      simpa only [Array.val_to_slice, Array.make, Array.from_val] using
        List.eq_getElem_of_length_eq_four bytes.val hlen
    obtain ⟨a,b,c,d,rfl⟩ := hform
    rw [source_decode_four]
    simp [resultToModel, ssz.decode.read_offset, Array.to_slice, Array.make]
  · rw [source_decode_wrong_length bytes hlen]
    simp [hlen, resultToModel, errorToModel]

/-- Source-level composition of the public reader, using the actual extracted
private decoder and the foundation slice-prefix operation. Direct extraction
of the public borrowed temporary remains unavailable. -/
private def readOffsetComposition (bytes : Slice U8) :
    Result (core.result.Result Usize milhouse.ssz.decode.DecodeError) := do
  let firstBytes ← core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
    bytes { start := 0#usize, «end» := 4#usize }
  match firstBytes with
  | none => ok (.Err (.InvalidLengthPrefix bytes.len 4#usize))
  | some firstBytes =>
    let value ← SszSource.ssz.decode.decode_offset firstBytes
    ok (resultToModel value)

theorem read_offset_composition_agrees (bytes : Slice U8) :
    readOffsetComposition bytes = ssz.decode.read_offset bytes := by
  obtain ⟨values, bound, rfl⟩ : ∃ (values : List U8)
      (bound : values.length ≤ Usize.max), bytes = Slice.from values bound :=
    ⟨bytes.val, bytes.property, (Slice.val_from bytes bytes.property).symm⟩
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals
    simp [readOffsetComposition, decode_offset_agrees, core.slice.Slice.get,
      core.slice.index.SliceIndexRangeUsizeSlice.get, ssz.decode.read_offset, Slice.len]

#print axioms width_agrees
#print axioms decode_offset_agrees
#print axioms read_offset_composition_agrees

private def sourceEncoderToModel (encoder : SszSource.ssz.encode.SszEncoder) : ssz.encode.SszEncoder :=
  ⟨encoder.offset, encoder.buf, encoder.variable_bytes⟩

private def modelEncoderToSource (encoder : ssz.encode.SszEncoder) : SszSource.ssz.encode.SszEncoder :=
  ⟨encoder.offset, encoder.buf, encoder.variable_bytes⟩

/-- Compare the actual constructor and its buffer-release continuation,
retaining the explicitly imported local Vec reserve foundation. -/
theorem container_agrees (buf : alloc.vec.Vec U8) (fixed : Usize) :
    (do let (encoder, release) ← SszSource.ssz.encode.SszEncoder.container buf fixed
        ok (sourceEncoderToModel encoder,
          fun replacement => release (modelEncoderToSource replacement))) =
      ssz.encode.SszEncoder.container buf fixed := by
  cases h : alloc.vec.Vec.reserve Global buf fixed <;>
    simp [SszSource.ssz.encode.SszEncoder.container, ssz.encode.SszEncoder.container,
      sourceEncoderToModel, modelEncoderToSource, h]

#print axioms container_agrees
