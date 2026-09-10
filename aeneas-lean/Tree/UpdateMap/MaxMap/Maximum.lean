import Tree.UpdateMap.MaxMap.Operations
import Tree.UpdateMap.Domain

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map.MaxMap

open Insts.MilhouseUpdate_mapUpdateMap

/-- The cache bounds every successfully observed pending key and, when
present, is itself attained by a pending value. This property imposes no
unrelated inner maximum-query law or totality requirement on all reads. -/
def MaximumValid {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M) : Prop :=
  MaximumBoundsValues mapInst self.inner self.max_index.toOption ∧
    ∀ last, self.max_index.toOption = some last →
      ∃ value, mapInst.get self.inner last = ok (some value)

theorem empty_maximum_valid_iff {T M : Type} (mapInst : UpdateMap M T) (inner : M) :
    (MaxMap.mk inner .Empty).MaximumValid mapInst ↔
      ∀ query value, mapInst.get inner query ≠ ok (some value) := by
  simp [MaximumValid, MaximumBoundsValues, MaxIndexState.toOption]

theorem known_maximum_valid_iff {T M : Type} (mapInst : UpdateMap M T)
    (inner : M) (last : Std.Usize) :
    (MaxMap.mk inner (.Known last)).MaximumValid mapInst ↔
      (∀ query value, mapInst.get inner query = ok (some value) → query.val ≤ last.val) ∧
      ∃ value, mapInst.get inner last = ok (some value) := by
  simp [MaximumValid, MaximumBoundsValues, MaxIndexState.toOption]

/-- A valid cache makes the actual public maximum result bound and attain
the keys observed by the wrapper's actual `get`. No inner maximum query runs. -/
theorem max_index_spec {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (hvalid : self.MaximumValid mapInst) :
    ∃ maximum, Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst self = ok maximum ∧
      (∀ query value, get mapInst self query = ok (some value) →
        ∃ last, maximum = some last ∧ query.val ≤ last.val) ∧
      ∀ last, maximum = some last → ∃ value, get mapInst self last = ok (some value) := by
  exact ⟨self.max_index.toOption, max_index_eq mapInst self, hvalid.1, hvalid.2⟩

/-- Successful default construction has a valid empty cache exactly when
the actual inner default succeeds and has no successfully observed values.
No unconditional empty-default law is assumed upfront. -/
theorem default_success_valid_iff {T M : Type} (mapInst : UpdateMap M T) :
    (∃ self, Insts.CoreDefaultDefault.default mapInst.coredefaultDefaultInst = ok self ∧
      self.MaximumValid mapInst) ↔
    ∃ inner, mapInst.coredefaultDefaultInst.default = ok inner ∧
      ∀ query value, mapInst.get inner query ≠ ok (some value) := by
  constructor
  · rintro ⟨self, hdefault, hvalid⟩
    rw [default_eq] at hdefault
    cases hinner : mapInst.coredefaultDefaultInst.default with
    | fail e => simp [hinner] at hdefault
    | div => simp [hinner] at hdefault
    | ok inner =>
      simp [hinner] at hdefault
      subst self
      exact ⟨inner, rfl, (empty_maximum_valid_iff mapInst inner).mp hvalid⟩
  · rintro ⟨inner, hinner, hempty⟩
    refine ⟨⟨inner, .Empty⟩, ?_, (empty_maximum_valid_iff mapInst inner).mpr hempty⟩
    rw [default_eq, hinner]
    rfl

/-- Actual insertion preserves the semantic maximum invariant from the
inner insertion's lookup frame. Neither its returned maximum metadata nor
an index/successor bound or cloning law is needed. -/
theorem insert_preserves_maximum_valid {T M : Type} (mapInst : UpdateMap M T)
    (self : MaxMap M) (index : Std.Usize) (value : T)
    (hvalid : self.MaximumValid mapInst)
    (hreads : ∀ previous inner,
      mapInst.insert self.inner index value = ok (previous, inner) →
      ∀ query, mapInst.get inner query =
        if query = index then ok (some value) else mapInst.get self.inner query)
    {previous : Option T} {updated : MaxMap M}
    (hinsert : insert mapInst self index value = ok (previous, updated)) :
    updated.MaximumValid mapInst := by
  obtain ⟨original, cached⟩ := self
  obtain ⟨inner, hinner, rfl⟩ := insert_result mapInst _ index value hinsert
  have hlookup := hreads previous inner hinner
  cases cached with
  | Empty =>
    have hempty := (empty_maximum_valid_iff mapInst original).mp hvalid
    apply (known_maximum_valid_iff mapInst inner index).mpr
    constructor
    · intro query found hget
      by_cases hquery : query = index
      · subst query; exact Nat.le_refl _
      · have hold : mapInst.get original query = ok (some found) := by
          simpa [hquery] using (hlookup query).symm.trans hget
        exact False.elim (hempty query found hold)
    · exact ⟨value, by simpa using hlookup index⟩
  | Known last =>
    obtain ⟨hbound, hattained⟩ := (known_maximum_valid_iff mapInst original last).mp hvalid
    apply (known_maximum_valid_iff mapInst inner (core.cmp.impls.OrdUsize.max last index)).mpr
    constructor
    · intro query found hget
      by_cases hquery : query = index
      · subst query
        simp only [core.cmp.impls.OrdUsize.max_val]
        exact Nat.le_max_right _ _
      · have hold : mapInst.get original query = ok (some found) := by
          simpa [hquery] using (hlookup query).symm.trans hget
        simp only [core.cmp.impls.OrdUsize.max_val]
        exact (hbound query found hold).trans (Nat.le_max_left _ _)
    · by_cases hlast : last.val ≤ index.val
      · have hmax : core.cmp.impls.OrdUsize.max last index = index := by
          apply UScalar.eq_of_val_eq
          simp [Nat.max_eq_right hlast]
        rw [hmax]
        exact ⟨value, by simpa using hlookup index⟩
      · have hmax : core.cmp.impls.OrdUsize.max last index = last := by
          apply UScalar.eq_of_val_eq
          simp [Nat.max_eq_left (by omega : index.val ≤ last.val)]
        have hne : last ≠ index := by intro heq; subst last; exact hlast (Nat.le_refl _)
        obtain ⟨found, hget⟩ := hattained
        rw [hmax]
        exact ⟨found, by simpa [hne, hget] using hlookup last⟩

/-- A successful inner insertion and its read frame give complete wrapper
execution, exact lookup replacement, and a still-valid maximum cache. -/
theorem insert_spec {T M : Type} (mapInst : UpdateMap M T)
    (self : MaxMap M) (index : Std.Usize) (value : T)
    (hvalid : self.MaximumValid mapInst)
    (hinner : ∃ previous inner, mapInst.insert self.inner index value = ok (previous, inner))
    (hreads : ∀ previous inner,
      mapInst.insert self.inner index value = ok (previous, inner) →
      ∀ query, mapInst.get inner query =
        if query = index then ok (some value) else mapInst.get self.inner query) :
    ∃ previous updated, insert mapInst self index value = ok (previous, updated) ∧
      updated.MaximumValid mapInst ∧
      (∀ query, get mapInst updated query =
        if query = index then ok (some value) else get mapInst self query) ∧
      Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst updated =
        ok (some (self.max_index.toOption.elim index (core.cmp.impls.OrdUsize.max index))) := by
  obtain ⟨previous, inner, hinner⟩ := hinner
  have hinsert := insert_success mapInst self index value hinner
  refine ⟨previous, _, hinsert,
    insert_preserves_maximum_valid mapInst self index value hvalid hreads hinsert, ?_,
    max_index_after_insert mapInst self index value hinsert⟩
  intro query
  exact get_after_insert mapInst self index query value
    (fun previous inner hinner => hreads previous inner hinner query) hinsert

end milhouse.update_map.MaxMap
