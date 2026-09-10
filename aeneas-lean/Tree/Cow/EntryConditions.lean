import Tree.Cow.EntrySuccess

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- Successful vector-entry insertion requires a representable successor
of its destination index. This follows from the actual growth arithmetic,
without assuming the slot is reachable from a represented list. -/
theorem vec_entry_insert_index_lt {T : Type} (entry : VecEntrySlot T)
    (value : T) {found : T} {back : T → VecEntrySlot T}
    (hinsert : vec_map.VacantEntry.insert entry value = ok (found, back)) :
    entry.index.val < Std.Usize.max := by
  unfold vec_map.VacantEntry.insert at hinsert
  by_cases hgrow : entry.backingLength ≤ entry.index
  · simp only [if_pos hgrow] at hinsert
    cases hdifference : entry.index - entry.backingLength with
    | fail e => simp [hdifference] at hinsert
    | div => simp [hdifference] at hinsert
    | ok difference =>
      cases hadded : difference + 1#usize with
      | fail e => simp [hdifference, hadded] at hinsert
      | div => simp [hdifference, hadded] at hinsert
      | ok added =>
        by_cases hbound : entry.backingLength.val + added.val ≤ Std.Usize.max
        · have hdifferenceVal := UScalar.sub_equiv entry.index entry.backingLength
          rw [hdifference] at hdifferenceVal
          have haddedVal := milhouse.tree.usize_add_val hadded
          scalar_tac
        · simp [hdifference, hadded, hbound] at hinsert
  · scalar_tac

/-- The destination successor bound is the exact success condition for
vector-entry insertion in the local collection model. Allocation behavior
remains abstracted by that model. -/
theorem vec_entry_insert_success_iff {T : Type} (entry : VecEntrySlot T) (value : T) :
    (∃ found back, vec_map.VacantEntry.insert entry value = ok (found, back)) ↔
      entry.index.val < Std.Usize.max := by
  constructor
  · rintro ⟨found, back, hinsert⟩
    exact vec_entry_insert_index_lt entry value hinsert
  · intro hindex
    obtain ⟨size, hinsert, _⟩ := vec_entry_insert_success entry value hindex
    exact ⟨value, _, hinsert⟩

end milhouse_models
