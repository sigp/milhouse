import Tree.Arbitrary.Models
import ArbitrarySource.Funs

open Aeneas Aeneas.Std Result

/-! Compare the actual bool/u8 generation and fill-buffer bodies with the local
collection-control model. The one-byte helper covers exactly the buffer width
used by this path; it is not a general fill-buffer theorem. -/

set_option maxHeartbeats 1000000 in
private theorem fill_buffer_one (input : Slice U8) (initial : U8) :
    ArbitrarySource.arbitrary.unstructured.Unstructured.fill_buffer { data := input }
      (Array.make 1#usize [initial]).to_slice =
    ok (.Ok (), { data := input.drop 1#usize },
      (Array.make 1#usize [input.val.headD 0#u8]).to_slice) := by
  obtain ⟨values, bound, rfl⟩ : ∃ (values : List U8)
      (bound : values.length ≤ Usize.max), input = Slice.from values bound :=
    ⟨input.val, input.property, (Slice.val_from input input.property).symm⟩
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
  simp [core.result.Result.Insts.CoreOpsTry.branch, core.num.U8.from_le_bytes,
    Array.from_slice, Array.to_slice, Array.make]
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, BitVec.toNat_cast]
  erw [Array.from_val, Slice.from_val]
  simp [BitVec.fromLEBytes]

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
  simp only [ArbitrarySource.Bool.Insts.ArbitraryArbitrary.arbitrary, byte_arbitrary,
    core.result.Result.Insts.CoreOpsTry.branch, lift, bind_tc_ok, resultToModel]
  unfold milhouse.arbitrary.nextControl
  split
  · rename_i h
    have hz : (0#u8) ≠ 1#u8 := by scalar_tac
    simp [h, hz, Slice.drop, Slice.eq_iff]
  · rename_i byte rest h
    simp [h, low_bit, Slice.drop]

private def errorFromModel : milhouse.arbitrary.error.Error → ArbitrarySource.arbitrary.error.SourceError
  | .EmptyChoose => .EmptyChoose
  | .NotEnoughData => .NotEnoughData
  | .IncorrectFormat => .IncorrectFormat

private def resultFromModel {T : Type} : core.result.Result T milhouse.arbitrary.error.Error →
    core.result.Result T ArbitrarySource.arbitrary.error.SourceError
  | .Ok value => .Ok value
  | .Err error => .Err (errorFromModel error)

/-- The complete callback dictionary, changing only input/error representations.
No generator, hint, or owning-input callback is replaced by a constant. -/
private def dictionaryToSource {T : Type} (inst : milhouse.arbitrary.Arbitrary T) :
    ArbitrarySource.arbitrary.Arbitrary T where
  generate_source := fun input => do
    let (value, after) ← inst.arbitrary input.data
    ok (resultFromModel value, { data := after })
  arbitrary_take_rest := fun input => do
    let value ← inst.arbitrary_take_rest input.data
    ok (resultFromModel value)
  size_hint := inst.size_hint
  try_size_hint := inst.try_size_hint

/-- The source default ignores all callbacks and every depth. -/
theorem size_hint_default_agrees {T : Type} (inst : milhouse.arbitrary.Arbitrary T)
    (depth : Usize) :
    ArbitrarySource.arbitrary.Arbitrary.size_hint.default T depth =
      milhouse.arbitrary.Arbitrary.size_hint.default inst depth := by rfl

/-- The source default calls the actual size-hint callback, preserving arbitrary
success, failure, and divergence, with no consistency or termination premise. -/
theorem try_size_hint_default_agrees {T : Type} (inst : milhouse.arbitrary.Arbitrary T)
    (depth : Usize) :
    ArbitrarySource.arbitrary.Arbitrary.try_size_hint.default (dictionaryToSource inst) depth =
      milhouse.arbitrary.Arbitrary.try_size_hint.default inst depth := by rfl

#print axioms control_agrees
#print axioms size_hint_default_agrees
#print axioms try_size_hint_default_agrees
