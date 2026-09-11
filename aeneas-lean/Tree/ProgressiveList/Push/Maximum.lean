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
      ∀ query, self.AppendReadAgrees ValueInst mapInst updates index value query)
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

/-- The complete append sequence postcondition is equivalent to the actual
returned maximum and per-query append agreement. No map-read law is assumed;
the source representation and successful execution supply the length bounds. -/
theorem ProgressiveList.push_represents_append_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (value : T)
    (hrep : self.Represents ValueInst mapInst contents)
    {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    pushed.Represents ValueInst mapInst (contents ++ [value]) ↔
      ∃ index : Std.Usize, index.val = contents.length ∧
        mapInst.max_index pushed.updates = ok (some index) ∧
        ∀ query, self.AppendReadAgrees ValueInst mapInst pushed.updates index value query := by
  obtain ⟨index, hlen, hcontentlen⟩ := hrep.1
  obtain ⟨previous, updates, hins, hpushed⟩ :=
    ProgressiveList.push_success ValueInst mapInst self value index hlen hpush
  constructor
  · intro hnew
    obtain ⟨length, hlength, hvalue⟩ := hnew.1
    have hnext : length.val = index.val + 1 := by
      simpa only [_root_.List.length_append, _root_.List.length_singleton, hcontentlen] using hvalue
    refine ⟨index, hcontentlen,
      (ProgressiveList.len_after_push_iff_max_index ValueInst mapInst self value index hlen hpush).mp
        ⟨length, hlength, hnext⟩, ?_⟩
    intro query
    rw [hpushed]
    apply (ProgressiveList.get_with_updates_append_eq_iff ValueInst mapInst self updates index value query
      (by intro heq; subst query
          exact ProgressiveList.len_ge_backing ValueInst mapInst self index hlen)).mp
    rw [← hpushed, hnew.2 query]
    by_cases heq : query = index
    · subst query
      rw [if_pos rfl, hcontentlen, _root_.List.getElem?_concat_length]
    · rw [if_neg heq, hrep.2 query]
      congr 1
      by_cases hlt : query.val < contents.length
      · exact _root_.List.getElem?_append_left hlt
      · have hne : query.val ≠ contents.length := by
          intro hvalue
          apply heq
          scalar_tac
        have hle : contents.length ≤ query.val := by omega
        rw [_root_.List.getElem?_append_right hle]
        have hold : contents[query.val]? = none := _root_.List.getElem?_eq_none_iff.mpr hle
        have hlast : [value][query.val - contents.length]? = none :=
          _root_.List.getElem?_eq_none_iff.mpr (by simp; omega)
        rw [hold, hlast]
  · rintro ⟨expected, hexpected, hmax, hreads⟩
    have heq : expected = index := by
      apply UScalar.eq_of_val_eq
      exact hexpected.trans hcontentlen.symm
    subst expected
    apply (ProgressiveList.push_represents_append_iff_max_index
      ValueInst mapInst self contents value hrep ?_ hpush).mpr ⟨index, hcontentlen, hmax⟩
    intro actual previous' updates' hactual hactualInsert
    rw [hlen] at hactual
    cases hactual
    rw [hins] at hactualInsert
    cases hactualInsert
    simpa only [hpushed] using hreads

end milhouse.progressive_list
