import Tree.UpdateMap.MaxMap.Operations

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map.MaxMap

open Insts.MilhouseUpdate_mapUpdateMap

/-- The returned mutable loan restores a missing inner loan unchanged, or
writes through a present loan and records its key. A missing replacement for
a present loan retains the original element in the reference abstraction. -/
def mutableBack {T M : Type} (self : MaxMap M) (index : Std.Usize)
    (found : Option T) (innerBack : Option T → M) (replacement : Option T) : MaxMap M :=
  match found with
  | none => { self with inner := innerBack none }
  | some original =>
    { inner := innerBack (some (replacement.getD original)),
      max_index := self.max_index.recorded index }

/-- Exact source equation, including inner failure/divergence and every
returned continuation input. Metadata recording itself is total. -/
theorem get_mut_with_eq {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F) :
    get_mut_with mapInst fnInst self index fallback = (do
      let (found, innerBack) ← mapInst.get_mut_with fnInst self.inner index fallback
      ok (found, mutableBack self index found innerBack)) := by
  unfold Insts.MilhouseUpdate_mapUpdateMap.get_mut_with
  cases mapInst.get_mut_with fnInst self.inner index fallback with
  | fail e => rfl
  | div => rfl
  | ok result =>
    obtain ⟨found, innerBack⟩ := result
    cases found with
    | none => rfl
    | some original =>
      simp only [bind_tc_ok, MaxIndexState.record_insert_eq]
      apply congrArg ok
      apply Prod.ext
      · rfl
      · funext replacement
        cases replacement <;> rfl

/-- The wrapper preserves the complete initial-value result of the inner
mutable call. No lookup, cloning, cache, or callback law is needed. -/
theorem get_mut_read_eq {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F) :
    (do let (found, _) ← get_mut_with mapInst fnInst self index fallback; ok found) =
      (do let (found, _) ← mapInst.get_mut_with fnInst self.inner index fallback; ok found) := by
  rw [get_mut_with_eq]
  cases mapInst.get_mut_with fnInst self.inner index fallback <;> rfl

/-- Successful wrapper access recovers the actual inner loan and the exact
write-back function without assumptions about either map's semantics. -/
theorem get_mut_result {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F)
    {found : Option T} {back : Option T → MaxMap M}
    (hcall : get_mut_with mapInst fnInst self index fallback = ok (found, back)) :
    ∃ innerBack, mapInst.get_mut_with fnInst self.inner index fallback = ok (found, innerBack) ∧
      back = mutableBack self index found innerBack := by
  rw [get_mut_with_eq] at hcall
  cases hinner : mapInst.get_mut_with fnInst self.inner index fallback with
  | fail e => simp [hinner] at hcall
  | div => simp [hinner] at hcall
  | ok result =>
    obtain ⟨actual, innerBack⟩ := result
    simp [hinner] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    exact ⟨innerBack, rfl, rfl⟩

theorem get_mut_succeeds_iff {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F) (found : Option T) :
    (∃ back, get_mut_with mapInst fnInst self index fallback = ok (found, back)) ↔
      ∃ innerBack, mapInst.get_mut_with fnInst self.inner index fallback = ok (found, innerBack) := by
  constructor
  · rintro ⟨back, hcall⟩
    obtain ⟨innerBack, hinner, _⟩ := get_mut_result mapInst fnInst self index fallback hcall
    exact ⟨innerBack, hinner⟩
  · rintro ⟨innerBack, hinner⟩
    refine ⟨mutableBack self index found innerBack, ?_⟩
    rw [get_mut_with_eq, hinner]
    rfl

/-- A present loan records the borrowed key even when its value is not
changed. The inner maximum-query operation and its laws are irrelevant. -/
theorem max_index_after_get_mut {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F)
    {original : T} {back : Option T → MaxMap M}
    (hcall : get_mut_with mapInst fnInst self index fallback = ok (some original, back))
    (replacement : Option T) :
    Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst (back replacement) =
      ok (some (self.max_index.toOption.elim index (core.cmp.impls.OrdUsize.max index))) := by
  obtain ⟨innerBack, _, rfl⟩ := get_mut_result mapInst fnInst self index fallback hcall
  rw [max_index_eq]
  exact congrArg ok (MaxIndexState.recorded_toOption self.max_index index)

/-- A missing loan leaves cached metadata unchanged for every continuation
input, independently of the inner map's missing-loan behavior. -/
theorem max_index_after_get_mut_missing {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F)
    {back : Option T → MaxMap M}
    (hcall : get_mut_with mapInst fnInst self index fallback = ok (none, back))
    (replacement : Option T) :
    Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst (back replacement) =
      Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst self := by
  obtain ⟨innerBack, _, rfl⟩ := get_mut_result mapInst fnInst self index fallback hcall
  rw [max_index_eq, max_index_eq]
  rfl

/-- Lookup frames transfer for the actual returned inner loan, one queried
key at a time. The replacement is a write through an existing element loan. -/
theorem get_after_get_mut {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index query : Std.Usize) (fallback : F)
    (original replacement : T)
    (hreads : ∀ innerBack,
      mapInst.get_mut_with fnInst self.inner index fallback = ok (some original, innerBack) →
      mapInst.get (innerBack (some replacement)) query =
        if query = index then ok (some replacement) else mapInst.get self.inner query)
    {back : Option T → MaxMap M}
    (hcall : get_mut_with mapInst fnInst self index fallback = ok (some original, back)) :
    get mapInst (back (some replacement)) query =
      if query = index then ok (some replacement) else get mapInst self query := by
  obtain ⟨innerBack, hinner, rfl⟩ := get_mut_result mapInst fnInst self index fallback hcall
  exact hreads innerBack hinner

/-- A missing wrapper loan restores the whole input whenever its actual
inner loan does. No law about present loans or unrelated fallbacks is used. -/
theorem get_mut_missing_restores {T M F : Type} (mapInst : UpdateMap M T)
    (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (self : MaxMap M) (index : Std.Usize) (fallback : F)
    (hmissing : ∀ innerBack,
      mapInst.get_mut_with fnInst self.inner index fallback = ok (none, innerBack) →
      innerBack none = self.inner)
    {back : Option T → MaxMap M}
    (hcall : get_mut_with mapInst fnInst self index fallback = ok (none, back)) :
    back none = self := by
  obtain ⟨innerBack, hinner, rfl⟩ := get_mut_result mapInst fnInst self index fallback hcall
  simp [mutableBack, hmissing innerBack hinner]

end milhouse.update_map.MaxMap
