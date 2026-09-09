import Tree.Arbitrary.Models
import ArbitrarySource.Funs

open Aeneas Aeneas.Std Result

/-! Compare the actual bool/u8 generation and fill-buffer bodies with the local
collection-control model. The one-byte helper covers exactly the buffer width
used by this path; it is not a general fill-buffer theorem. -/

private theorem fill_buffer_one (input : Slice U8) (initial : U8) :
    ArbitrarySource.arbitrary.unstructured.Unstructured.fill_buffer { data := input }
      (Array.make 1#usize [initial]).to_slice =
    ok (.Ok (), { data := input.drop 1#usize },
      (Array.make 1#usize [input.val.headD 0#u8]).to_slice) := by
  rcases input with ⟨values, bound⟩
  rcases values with _ | ⟨byte, _ | ⟨next, rest⟩⟩
  all_goals
    simp [ArbitrarySource.arbitrary.unstructured.Unstructured.fill_buffer,
      core.cmp.min, core.cmp.impls.OrdUsize.min,
      core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
      core.slice.index.SliceIndexRangeToUsizeSlice.index,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index,
      core.slice.Slice.copy_from_slice, core.slice.Slice.iter_mut,
      Array.to_slice, Array.make, Slice.len, Slice.drop, List.setSlice!]
  all_goals
    simp only [ArbitrarySource.arbitrary.unstructured.Unstructured.fill_buffer_loop]
    rw [loop]
    simp [ArbitrarySource.arbitrary.unstructured.Unstructured.fill_buffer_loop.body,
      core.slice.iter.IteratorIterMut.next, Slice.len, Slice.setAtNat]
  rw [loop]
  simp

private theorem byte_arbitrary (input : Slice U8) :
    ArbitrarySource.U8.Insts.ArbitraryArbitrary.arbitrary { data := input } =
      ok (.Ok (input.val.headD 0#u8), { data := input.drop 1#usize }) := by
  simp [ArbitrarySource.U8.Insts.ArbitraryArbitrary.arbitrary,
    Array.to_slice_mut, lift]
  rw [show ArbitrarySource.arbitrary.unstructured.Unstructured.fill_buffer
      { data := input } (Array.repeat 1#usize 0#u8).to_slice = _ from fill_buffer_one input 0#u8]
  simp [core.result.Result.Insts.CoreOpsTry.branch, core.num.U8.from_le_bytes, BitVec.fromLEBytes,
    Array.from_slice, Array.to_slice, Array.make]

private theorem low_bit (byte : U8) :
    (byte &&& 1#u8 = 1#u8) ↔ byte.val % 2 = 1 := by
  have hv : (byte &&& 1#u8).val = byte.val % 2 := by
    change (byte.bv &&& 1#8).toNat = byte.bv.toNat % 2
    simp
  constructor
  · intro h
    have hval : (byte &&& 1#u8).val = 1 := congrArg UScalar.val h
    rwa [hv] at hval
  · intro h
    apply UScalar.eq_of_val_eq
    change (byte &&& 1#u8).val = 1
    rwa [hv]

private def errorToModel : ArbitrarySource.arbitrary.error.SourceError → milhouse.arbitrary.error.Error
  | .EmptyChoose => .EmptyChoose
  | .NotEnoughData => .NotEnoughData
  | .IncorrectFormat => .IncorrectFormat

private def resultToModel : core.result.Result Bool ArbitrarySource.arbitrary.error.SourceError →
    core.result.Result Bool milhouse.arbitrary.error.Error
  | .Ok value => .Ok value
  | .Err error => .Err (errorToModel error)

/-- Complete control read, including error mapping and final input. No input
length, successful-read, or termination hypothesis is required. -/
theorem control_agrees (input : Slice U8) :
    (do let (value, after) ← ArbitrarySource.Bool.Insts.ArbitraryArbitrary.arbitrary { data := input }
        ok (resultToModel value, after.data)) =
      ok (.Ok (milhouse.arbitrary.nextControl input).1, (milhouse.arbitrary.nextControl input).2) := by
  simp only [ArbitrarySource.Bool.Insts.ArbitraryArbitrary.arbitrary, byte_arbitrary]
  rcases input with ⟨values, bound⟩
  cases values with
  | nil => simp [core.result.Result.Insts.CoreOpsTry.branch, lift, resultToModel, milhouse.arbitrary.nextControl, Slice.drop]
  | cons byte rest => simp [core.result.Result.Insts.CoreOpsTry.branch, lift, resultToModel, milhouse.arbitrary.nextControl, Slice.drop, low_bit]

#print axioms control_agrees
