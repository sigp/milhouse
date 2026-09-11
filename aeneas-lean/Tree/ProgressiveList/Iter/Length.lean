import Tree.ProgressiveList.Iter.Next

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem saturating_sub_val (length index : Std.Usize) :
    (core.num.Usize.saturating_sub length index).val = length.val - index.val := by
  change (length.val - index.val) % 2 ^ UScalarTy.Usize.numBits = length.val - index.val
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- Both size-hint bounds equal the exact length of the represented suffix.
    Only the recorded length's agreement with the sequence is required; no
    tree or map assumptions enter this arithmetic observer. -/
theorem ProgressiveListIter.size_hint_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (contents : _root_.List T)
    (hlength : self.length.val = contents.length) :
    ∃ remaining,
      ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.size_hint ValueInst mapInst self =
        ok (remaining, some remaining) ∧
      remaining.val = (contents.drop self.index.val).length := by
  refine ⟨core.num.Usize.saturating_sub self.length self.index, rfl, ?_⟩
  rw [saturating_sub_val, hlength, _root_.List.length_drop]

/-- `ExactSizeIterator::len` returns the exact represented suffix length,
    including zero at and beyond the end. -/
theorem ProgressiveListIter.exact_len_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (contents : _root_.List T)
    (hlength : self.length.val = contents.length) :
    ∃ remaining,
      ProgressiveListIter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT.len ValueInst mapInst self =
        ok remaining ∧ remaining.val = (contents.drop self.index.val).length := by
  obtain ⟨remaining, hsize, hremaining⟩ := ProgressiveListIter.size_hint_spec ValueInst mapInst self contents hlength
  refine ⟨remaining, ?_, hremaining⟩
  simp! only [ProgressiveListIter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT.len,
    hsize, bind_tc_ok]

end milhouse.progressive_list
