import Tree.ProgressiveList.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Under the insertion's lookup law, correct sequence append is equivalent
to exact returned maximum metadata. The read law concerns only the actual
insertion; no successful maximum query or capacity bound is assumed. This
proves the metadata premise of the total append contract is necessary. -/
theorem ProgressiveList.push_represents_append_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (value : T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hinsert_get : ∀ index previous updates,
      ProgressiveList.len ValueInst mapInst self = ok index →
      mapInst.insert self.updates index value = ok (previous, updates) →
      ∀ query, mapInst.get updates query =
        if query = index then ok (some value) else mapInst.get self.updates query)
    {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    pushed.Represents ValueInst mapInst (contents ++ [value]) ↔
      ∃ index : Std.Usize, index.val = contents.length ∧
        mapInst.max_index pushed.updates = ok (some index) := by
  obtain ⟨index, hlen, hcontentlen⟩ := hrep.1
  constructor
  · intro hnew
    obtain ⟨length, hlength, hvalue⟩ := hnew.1
    have hnext : length.val = index.val + 1 := by
      simpa only [_root_.List.length_append, _root_.List.length_singleton, hcontentlen] using hvalue
    exact ⟨index, hcontentlen,
      (ProgressiveList.len_after_push_iff_max_index ValueInst mapInst self value index hlen hpush).mp
        ⟨length, hlength, hnext⟩⟩
  · rintro ⟨expected, hexpected, hmax⟩
    have heq : expected = index := by
      apply UScalar.eq_of_val_eq
      exact hexpected.trans hcontentlen.symm
    subst expected
    obtain ⟨previous, updates, hins, hpushed⟩ :=
      ProgressiveList.push_success ValueInst mapInst self value index hlen hpush
    apply ProgressiveList.push_represents_append ValueInst mapInst self contents value hrep ?_ hpush
    intro actual previous' updates' hactual hactualInsert
    rw [hlen] at hactual
    cases hactual
    rw [hins] at hactualInsert
    cases hactualInsert
    exact ⟨by simpa only [hpushed] using hmax, hinsert_get index previous updates hlen hins⟩

end milhouse.progressive_list
