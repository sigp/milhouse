import Tree.Rebase.Steps

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- The minimum of two lengths always succeeds and stays below both inputs.
No relation between recorded lengths and tree contents is needed. -/
theorem length_min_success (left right : utils.Length) :
    ∃ minimum, core.cmp.min utils.Length.Insts.CoreCmpOrd left right = ok minimum ∧
      minimum.val = min left.val right.val := by
  simp only [core.cmp.min,
    core.cmp.Ord.min.default, core.cmp.Ord.min_body,
    core.cmp.PartialOrd.lt_body,
    utils.Length.Insts.CoreCmpPartialOrdLength.partial_cmp,
    utils.Length.Insts.CoreCmpOrd.cmp, core.cmp.impls.OrdUsize.cmp,
    Bind.bind, Std.bind]
  split <;> simp_all [Nat.compare_eq_lt, Nat.min_def] <;> omega

/-- Every checked operation in the rebase length split succeeds under the
shift's actual word-size bound. Lengths may exceed the subtree capacity: each
left side is clamped and each right side is the exact remaining suffix. -/
theorem rebase_split_lengths_success {T : Type} (ValueInst : Value T)
    (origLength baseLength newDepth : Std.Usize)
    (hshift : newDepth.val < UScalarTy.Usize.numBits) :
    ∃ origLeft baseLeft origRight baseRight,
      Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once
        ValueInst newDepth (origLength, baseLength) = ok ((origLeft, baseLeft), (origRight, baseRight)) ∧
      origLeft.val = min origLength.val (2 ^ newDepth.val) ∧
      baseLeft.val = min baseLength.val (2 ^ newDepth.val) ∧
      origRight.val = origLength.val - 2 ^ newDepth.val ∧
      baseRight.val = baseLength.val - 2 ^ newDepth.val := by
  obtain ⟨capacity, hcapacity, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec 1#usize newDepth (UScalar.size .Usize) hshift rfl)
  have hcapacityVal := usize_shift_left_one_val hcapacity
  obtain ⟨origLeft, horigLeft, horigLeftVal⟩ := length_min_success origLength capacity
  obtain ⟨baseLeft, hbaseLeft, hbaseLeftVal⟩ := length_min_success baseLength capacity
  obtain ⟨origRight, horigRight, horigRightVal, _⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := origLength) (y := origLeft) (by scalar_tac))
  obtain ⟨baseRight, hbaseRight, hbaseRightVal, _⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := baseLength) (y := baseLeft) (by scalar_tac))
  refine ⟨origLeft, baseLeft, origRight, baseRight, ?_, ?_, ?_, ?_, ?_⟩
  · simp! only [Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once,
      hcapacity, horigLeft, hbaseLeft, utils.Length.as_usize, horigRight, hbaseRight, bind_tc_ok]
  · simpa only [hcapacityVal] using horigLeftVal
  · simpa only [hcapacityVal] using hbaseLeftVal
  · rw [horigRightVal, horigLeftVal, hcapacityVal]
    omega
  · rw [hbaseRightVal, hbaseLeftVal, hcapacityVal]
    omega

end milhouse.tree
