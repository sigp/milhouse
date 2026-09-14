import Tree.Cow.Metadata

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- The optional maximum represented by the wrapper's cached state. -/
def MaxIndexState.toOption : MaxIndexState → Option Std.Usize
  | .Empty => none
  | .Known index => some index

/-- Recording a key takes its maximum with the previous cached key. -/
theorem MaxIndexState.recorded_toOption (self : MaxIndexState) (index : Std.Usize) :
    (self.recorded index).toOption =
      some (self.toOption.elim index (core.cmp.impls.OrdUsize.max index)) := by
  cases self with
  | Empty => rfl
  | Known previous =>
    simp only [recorded, toOption, Option.elim_some]
    congr 1
    apply UScalar.eq_of_val_eq
    simp [Nat.max_comm]

namespace MaxMap

open Insts.MilhouseUpdate_mapUpdateMap

/-- Default construction preserves the actual inner default result and
starts with an empty maximum cache, including failure and divergence. -/
theorem default_eq {M : Type} (defaultInst : core.default.Default M) :
    Insts.CoreDefaultDefault.default defaultInst = (do
      let inner ← defaultInst.default
      ok ({ inner, max_index := .Empty } : MaxMap M)) := by
  unfold Insts.CoreDefaultDefault.default MaxIndexState.Insts.CoreDefaultDefault.default
  cases defaultInst.default <;> rfl

/-- Lookup delegates to the inner map without observing maximum metadata. -/
theorem get_eq {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M) (index : Std.Usize) :
    get mapInst self index = mapInst.get self.inner index := rfl

/-- Cardinality delegates to the inner map without observing maximum metadata. -/
theorem len_eq {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M) :
    len mapInst self = mapInst.len self.inner := rfl

/-- The maximum query reads only cached metadata; it does not call the inner
maximum query or require its termination or correctness. -/
theorem max_index_eq {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M) :
    Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst self = ok self.max_index.toOption := by
  unfold Insts.MilhouseUpdate_mapUpdateMap.max_index
  cases self.max_index <;> rfl

/-- Insertion propagates the complete inner result, then records the key.
The old optional value is returned unchanged and metadata recording is total. -/
theorem insert_eq {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (index : Std.Usize) (value : T) :
    insert mapInst self index value = (do
      let (previous, inner) ← mapInst.insert self.inner index value
      ok (previous, { inner, max_index := self.max_index.recorded index })) := by
  unfold Insts.MilhouseUpdate_mapUpdateMap.insert
  cases mapInst.insert self.inner index value with
  | fail e => rfl
  | div => rfl
  | ok result =>
    obtain ⟨previous, inner⟩ := result
    simp only [bind_tc_ok, MaxIndexState.record_insert_eq]

theorem insert_success {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (index : Std.Usize) (value : T) {previous : Option T} {inner : M}
    (hinner : mapInst.insert self.inner index value = ok (previous, inner)) :
    insert mapInst self index value =
      ok (previous, { inner, max_index := self.max_index.recorded index }) := by
  rw [insert_eq, hinner]
  rfl

/-- Recover the actual inner insertion and exact cached state from any
successful wrapper result. No map or maximum-validity laws are assumed. -/
theorem insert_result {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (index : Std.Usize) (value : T) {previous : Option T} {updated : MaxMap M}
    (hinsert : insert mapInst self index value = ok (previous, updated)) :
    ∃ inner, mapInst.insert self.inner index value = ok (previous, inner) ∧
      updated = { inner, max_index := self.max_index.recorded index } := by
  rw [insert_eq] at hinsert
  cases hinner : mapInst.insert self.inner index value with
  | fail e => simp [hinner] at hinsert
  | div => simp [hinner] at hinsert
  | ok result =>
    obtain ⟨found, inner⟩ := result
    simp [hinner] at hinsert
    obtain ⟨rfl, rfl⟩ := hinsert
    exact ⟨inner, rfl, rfl⟩

/-- Wrapper insertion succeeds exactly when the inner insertion succeeds. -/
theorem insert_succeeds_iff {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (index : Std.Usize) (value : T) :
    (∃ previous updated, insert mapInst self index value = ok (previous, updated)) ↔
      ∃ previous inner, mapInst.insert self.inner index value = ok (previous, inner) := by
  constructor
  · rintro ⟨previous, updated, hinsert⟩
    obtain ⟨inner, hinner, _⟩ := insert_result mapInst self index value hinsert
    exact ⟨previous, inner, hinner⟩
  · rintro ⟨previous, inner, hinner⟩
    exact ⟨previous, _, insert_success mapInst self index value hinner⟩

/-- The actual wrapper enforces the exact insertion-maximum law without
any inner maximum-query law, cache-validity invariant, or index bound. -/
theorem max_index_after_insert {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (index : Std.Usize) (value : T) {previous : Option T} {updated : MaxMap M}
    (hinsert : insert mapInst self index value = ok (previous, updated)) :
    Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst updated =
      ok (some (self.max_index.toOption.elim index (core.cmp.impls.OrdUsize.max index))) := by
  obtain ⟨inner, _, rfl⟩ := insert_result mapInst self index value hinsert
  rw [max_index_eq, MaxIndexState.recorded_toOption]

/-- Pointwise lookup behavior transfers from the actual inner insertion.
Failure and divergence at other queried keys are preserved too. -/
theorem get_after_insert {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (index query : Std.Usize) (value : T)
    (hreads : ∀ previous inner,
      mapInst.insert self.inner index value = ok (previous, inner) →
      mapInst.get inner query = if query = index then ok (some value) else mapInst.get self.inner query)
    {previous : Option T} {updated : MaxMap M}
    (hinsert : insert mapInst self index value = ok (previous, updated)) :
    get mapInst updated query = if query = index then ok (some value) else get mapInst self query := by
  obtain ⟨inner, hinner, rfl⟩ := insert_result mapInst self index value hinsert
  exact hreads previous inner hinner

end MaxMap
end milhouse.update_map
