import Tree.ProgressiveList.Mutable.FallbackTotal

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem projected_success_iff {A B : Type} (result : Result (A × B)) (value : A) :
    (∃ back, result = ok (value, back)) ↔
      (do let (found, _) ← result
          ok found) = ok value := by
  cases result with
  | fail error => simp
  | div => simp
  | ok pair => cases pair; simp [eq_comm]

/-- Exact successful-value criterion under the read law for this actual
fallback only. A pending value is returned directly; absent pending data
requires a successful backing read and, only when that read finds a value,
a successful clone. No representation, tree invariant, clone law, write law,
or successful internal call is assumed outside the criterion. -/
theorem ProgressiveList.get_mut_value_success_iff_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (found : Option T)
    (hreads : self.GetMutReads ValueInst mapInst index) :
    (∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (found, back)) ↔
      (∃ pending, mapInst.get self.updates index = ok (some pending) ∧ found = some pending) ∨
      (mapInst.get self.updates index = ok none ∧
        ((ProgressiveList.backing_get ValueInst mapInst self index = ok none ∧ found = none) ∨
         ∃ original cloned, ProgressiveList.backing_get ValueInst mapInst self index = ok (some original) ∧
           ValueInst.corecloneCloneInst.clone original = ok cloned ∧ found = some cloned)) := by
  rw [projected_success_iff]
  erw [ProgressiveList.get_mut_read_eq_pending_or_clone_of_fallback ValueInst mapInst self index hreads]
  cases mapInst.get self.updates index with
  | fail error => simp
  | div => simp
  | ok pending =>
    cases pending with
    | some pending => simp [eq_comm]
    | none =>
      cases ProgressiveList.backing_get ValueInst mapInst self index with
      | fail error => simp
      | div => simp
      | ok backing =>
        cases backing with
        | none => simp [core.option.OptionShared0T.cloned, eq_comm]
        | some original =>
          cases hclone : ValueInst.corecloneCloneInst.clone original <;>
            simp [core.option.OptionShared0T.cloned, hclone, eq_comm]

/-- Mutable lookup terminates successfully exactly for these reached input
outcomes. In particular, missing backing data needs no clone and pending data
needs no backing read. Failure or divergence of a required call prevents
success. No write-back or maximum-index law is needed for acquisition. -/
theorem ProgressiveList.get_mut_success_iff_inputs_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetMutReads ValueInst mapInst index) :
    (∃ found back, ProgressiveList.get_mut ValueInst mapInst self index = ok (found, back)) ↔
      (∃ pending, mapInst.get self.updates index = ok (some pending)) ∨
      (mapInst.get self.updates index = ok none ∧
        (ProgressiveList.backing_get ValueInst mapInst self index = ok none ∨
         ∃ original cloned, ProgressiveList.backing_get ValueInst mapInst self index = ok (some original) ∧
           ValueInst.corecloneCloneInst.clone original = ok cloned)) := by
  constructor
  · rintro ⟨found, back, hmut⟩
    rcases (ProgressiveList.get_mut_value_success_iff_of_fallback
      ValueInst mapInst self index found hreads).mp ⟨back, hmut⟩ with
      ⟨pending, hpending, _⟩ | ⟨hpending, hbacking⟩
    · exact Or.inl ⟨pending, hpending⟩
    · refine Or.inr ⟨hpending, ?_⟩
      rcases hbacking with ⟨hmissing, _⟩ | ⟨original, cloned, hbacking, hclone, _⟩
      · exact Or.inl hmissing
      · exact Or.inr ⟨original, cloned, hbacking, hclone⟩
  · rintro (⟨pending, hpending⟩ | ⟨hpending, hbacking⟩)
    · obtain ⟨back, hmut⟩ := (ProgressiveList.get_mut_value_success_iff_of_fallback
        ValueInst mapInst self index (some pending) hreads).mpr (Or.inl ⟨pending, hpending, rfl⟩)
      exact ⟨some pending, back, hmut⟩
    · rcases hbacking with hmissing | ⟨original, cloned, hbacking, hclone⟩
      · obtain ⟨back, hmut⟩ := (ProgressiveList.get_mut_value_success_iff_of_fallback
          ValueInst mapInst self index none hreads).mpr (Or.inr ⟨hpending, Or.inl ⟨hmissing, rfl⟩⟩)
        exact ⟨none, back, hmut⟩
      · obtain ⟨back, hmut⟩ := (ProgressiveList.get_mut_value_success_iff_of_fallback
          ValueInst mapInst self index (some cloned) hreads).mpr
          (Or.inr ⟨hpending, Or.inr ⟨original, cloned, hbacking, hclone, rfl⟩⟩)
        exact ⟨some cloned, back, hmut⟩

/-- For an actually present immutable read, the fallback clone's termination
is necessary as well as sufficient for successful mutable acquisition. The
condition is vacuous for an existing pending value; clone identity, map laws
for other fallbacks, and backing/length invariants are unnecessary. -/
theorem ProgressiveList.get_mut_present_success_iff_clone_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (old : T)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok (some old)) :
    (∃ value back, ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) ↔
      (mapInst.get self.updates index = ok none →
        ∃ value, ValueInst.corecloneCloneInst.clone old = ok value) := by
  constructor
  · rintro ⟨value, back, hmut⟩ hpending
    rcases (ProgressiveList.get_mut_value_success_iff_of_fallback
      ValueInst mapInst self index (some value) hreads).mp ⟨back, hmut⟩ with
      ⟨pending, hfound, _⟩ | ⟨_, hbacking⟩
    · simp only [hpending, Result.ok.injEq, reduceCtorEq] at hfound
    · rcases hbacking with ⟨_, himpossible⟩ | ⟨original, cloned, hbacking, hclone, _⟩
      · cases himpossible
      · have horiginal : original = old := by
          simpa only [ProgressiveList.get, hpending, bind_tc_ok, hbacking,
            Result.ok.injEq, Option.some.injEq] using hget
        subst original
        exact ⟨cloned, hclone⟩
  · intro hclone
    obtain ⟨value, back, hmut, _⟩ := ProgressiveList.get_mut_present_succeeds_of_fallback
      ValueInst mapInst self index old hreads hget hclone
    exact ⟨value, back, hmut⟩

end milhouse.progressive_list
