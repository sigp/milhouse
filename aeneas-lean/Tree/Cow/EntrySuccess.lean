import Tree.Cow.EntryModels
import Tree.Arithmetic

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- A vector-map vacant slot below the maximum machine index can always be
materialized. Growth arithmetic is derived from that single index bound;
the exact new backing length and final stored value are retained. -/
theorem vec_entry_insert_success {T : Type} (entry : VecEntrySlot T) (value : T)
    (hindex : entry.index.val < Std.Usize.max) :
    ∃ size, vec_map.VacantEntry.insert entry value =
      ok (value, fun replacement => { entry with backingLength := size, value := some replacement }) ∧
      size.val = max entry.backingLength.val (entry.index.val + 1) := by
  unfold vec_map.VacantEntry.insert
  by_cases hgrow : entry.backingLength ≤ entry.index
  · obtain ⟨difference, hdifference, hdifferenceVal, _⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := entry.index) (y := entry.backingLength) (by scalar_tac))
    obtain ⟨added, hadded, haddedVal⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := difference) (y := 1#usize) (by scalar_tac))
    have hsize : entry.backingLength.val + added.val = entry.index.val + 1 := by
      simp at haddedVal
      scalar_tac
    have hbound : entry.backingLength.val + added.val ≤ Std.Usize.max := by omega
    simp only [if_pos hgrow, hdifference, hadded, bind_tc_ok, dif_pos hbound]
    refine ⟨_, rfl, ?_⟩
    simp only [UScalar.ofNatCore_val_eq, hsize]
    exact (max_eq_right (by scalar_tac)).symm
  · refine ⟨entry.backingLength, ?_, ?_⟩
    · simp only [if_neg hgrow, bind_tc_ok]
    · exact (max_eq_left (by scalar_tac)).symm

end milhouse_models
