import Tree.Cow.Consuming
import Tree.Cow.EntryConditions

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- Actual consuming success supplies the entry/growth conditions and the
exact initial value. Immutable handles return their actual clone result;
mutable handles return their existing value. No entry or clone law is assumed. -/
theorem Cow.into_mut_inputs_of_success {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) {value : T} {back : core.result.Result T error.Error → Cow T}
    (hmut : Cow.into_mut cloneInst self = ok (.Ok value, back)) :
    self.CanMaterialize ∧ self.MaterializedValue cloneInst value := by
  cases self with
  | BTree inner action =>
    cases inner with
    | Mutable original =>
      simp [Cow.into_mut, BTreeCow.into_mut_inner, CowOnMut.run_eq] at hmut
      obtain ⟨rfl, _⟩ := hmut
      exact ⟨trivial, rfl⟩
    | Immutable original entry =>
      cases entry with
      | none => simp [Cow.into_mut, BTreeCow.into_mut_inner] at hmut
      | some entry =>
        cases hclone : cloneInst.clone original with
        | fail e => simp [Cow.into_mut, BTreeCow.into_mut_inner, hclone] at hmut
        | div => simp [Cow.into_mut, BTreeCow.into_mut_inner, hclone] at hmut
        | ok cloned =>
          simp [Cow.into_mut, BTreeCow.into_mut_inner, hclone,
            alloc.collections.btree.map.entry.VacantEntry.insert, CowOnMut.run_eq] at hmut
          obtain ⟨rfl, _⟩ := hmut
          exact ⟨rfl, hclone⟩
  | Vec inner action =>
    cases inner with
    | Mutable original =>
      simp [Cow.into_mut, VecCow.into_mut_inner, CowOnMut.run_eq] at hmut
      obtain ⟨rfl, _⟩ := hmut
      exact ⟨trivial, rfl⟩
    | Immutable original entry =>
      cases entry with
      | none => simp [Cow.into_mut, VecCow.into_mut_inner] at hmut
      | some entry =>
        cases hclone : cloneInst.clone original with
        | fail e => simp [Cow.into_mut, VecCow.into_mut_inner, hclone] at hmut
        | div => simp [Cow.into_mut, VecCow.into_mut_inner, hclone] at hmut
        | ok cloned =>
          cases hinsert : vec_map.VacantEntry.insert entry cloned with
          | fail e => simp [Cow.into_mut, VecCow.into_mut_inner, hclone, hinsert] at hmut
          | div => simp [Cow.into_mut, VecCow.into_mut_inner, hclone, hinsert] at hmut
          | ok result =>
            obtain ⟨found, entryBack⟩ := result
            have hindex := milhouse_models.vec_entry_insert_index_lt entry cloned hinsert
            obtain ⟨size, hinsertExact, _⟩ :=
              milhouse_models.vec_entry_insert_success entry cloned hindex
            simp [Cow.into_mut, VecCow.into_mut_inner, hclone,
              hinsertExact, CowOnMut.run_eq] at hmut
            obtain ⟨rfl, _⟩ := hmut
            exact ⟨hindex, hclone⟩

/-- Entry readiness and the exact materialized value characterize consuming
success. These conditions are both necessary and sufficient, including the
vector growth bound; no list representation or key-location premise is needed. -/
theorem Cow.into_mut_value_success_iff {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (value : T) :
    (∃ back, Cow.into_mut cloneInst self = ok (.Ok value, back)) ↔
      self.CanMaterialize ∧ self.MaterializedValue cloneInst value := by
  constructor
  · rintro ⟨back, hmut⟩
    exact Cow.into_mut_inputs_of_success cloneInst self hmut
  · rintro ⟨hready, hvalue⟩
    obtain ⟨back, hmut, _⟩ := Cow.into_mut_spec cloneInst self value hready hvalue
    exact ⟨back, hmut⟩

/-- Consuming success needs precisely a materializable entry and termination
of the actual clone on the immutable branch. No clone is required on a
mutable branch, and the clone need not preserve the original value. -/
theorem Cow.into_mut_success_iff {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) :
    (∃ value back, Cow.into_mut cloneInst self = ok (.Ok value, back)) ↔
      self.CanMaterialize ∧
        (self.NeedsClone = true → ∃ value, cloneInst.clone self.value = ok value) := by
  constructor
  · rintro ⟨value, back, hmut⟩
    obtain ⟨hready, hvalue⟩ := Cow.into_mut_inputs_of_success cloneInst self hmut
    refine ⟨hready, ?_⟩
    intro hneeds
    cases self with
    | BTree inner action =>
      cases inner with
      | Immutable original entry => exact ⟨value, hvalue⟩
      | Mutable original => cases hneeds
    | Vec inner action =>
      cases inner with
      | Immutable original entry => exact ⟨value, hvalue⟩
      | Mutable original => cases hneeds
  · rintro ⟨hready, hclone⟩
    obtain ⟨value, back, hmut, _⟩ := Cow.into_mut_success cloneInst self hready hclone
    exact ⟨value, back, hmut⟩

/-- The continuation returned by any actual consuming success has the
proved filled-entry and maximum-index footprint. Readiness and cloning are
recovered from execution rather than supplied as extra assumptions. -/
theorem Cow.into_mut_written_of_success {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) {value : T} {back : core.result.Result T error.Error → Cow T}
    (hmut : Cow.into_mut cloneInst self = ok (.Ok value, back)) :
    ∀ replacement, self.Written replacement (back (.Ok replacement)) := by
  obtain ⟨hready, hvalue⟩ := Cow.into_mut_inputs_of_success cloneInst self hmut
  obtain ⟨expected, hexpected, hwritten⟩ := Cow.into_mut_spec cloneInst self value hready hvalue
  have heq : expected = back := by simpa [hmut] using hexpected.symm
  simpa only [heq] using hwritten

end milhouse.cow
