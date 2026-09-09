import Tree.ProgressiveList.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Raw map outcomes describe replacement of one selected value and unchanged
other reads after the original backing fallback. No public read or successful
fallback call is assumed. -/
def ProgressiveList.SetReadsAgree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (updates : U) (index : Std.Usize) (replacement : T) : Prop :=
  ∀ query, update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
    (mapInst.get updates query)
    (if query = index then ok (some replacement) else mapInst.get self.updates query)

/-- Exact sequence-replacement criterion for a returned pending map. The
source representation and selected-element bound are the only sequence
premises. Raw lookup agreement and maximum-result agreement are jointly
necessary and sufficient; neither map law is assumed in the equivalence. -/
theorem ProgressiveList.represents_set_with_updates_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (updates : U) (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length) :
    ({ self with updates } : ProgressiveList T U).Represents ValueInst mapInst
      (contents.set index.val replacement) ↔
      utils.MaxIndexResultsAgree self.length (mapInst.max_index updates) (mapInst.max_index self.updates) ∧
        self.SetReadsAgree ValueInst mapInst updates index replacement := by
  obtain ⟨length, hlen, hvalue⟩ := hrep.1
  constructor
  · intro hnew
    obtain ⟨newLength, hnewLength, hnewValue⟩ := hnew.1
    have hsame : newLength = length := by
      apply UScalar.eq_of_val_eq
      simpa only [_root_.List.length_set, hvalue] using hnewValue
    refine ⟨(ProgressiveList.len_with_updates_eq_iff_max_index ValueInst mapInst self updates).mp
      (by rw [hnewLength, hlen, hsame]), ?_⟩
    intro query
    apply (ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self updates index query replacement).mp
    rw [hnew.2 query]
    by_cases heq : query = index
    · subst query
      simp [hindex]
    · rw [if_neg heq, hrep.2 query]
      have hne : index.val ≠ query.val := by intro h; apply heq; scalar_tac
      simp [hne]
  · rintro ⟨hmax, hreads⟩
    refine ⟨⟨length, ((ProgressiveList.len_with_updates_eq_iff_max_index
      ValueInst mapInst self updates).mpr hmax).trans hlen, by simpa using hvalue⟩, ?_⟩
    intro query
    rw [(ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self updates index query replacement).mpr
      (hreads query)]
    by_cases heq : query = index
    · subst query
      simp [hindex]
    · rw [if_neg heq, hrep.2 query]
      have hne : index.val ≠ query.val := by intro h; apply heq; scalar_tac
      simp [hne]

end milhouse.progressive_list
