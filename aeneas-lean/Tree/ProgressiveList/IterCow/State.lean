import Tree.ProgressiveList.Backing
import Tree.ProgressiveList.IterCow.Bounds

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private theorem unchecked_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {cursor : ProgressiveListIterCow T U} {back : ProgressiveListIterCow T U → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow_from_unchecked ValueInst mapInst self index = ok (cursor, back)) :
    cursor.index = index ∧ cursor.updates = self.updates ∧
      back = fun replacement => { self with updates := replacement.updates } := by
  simp only [ProgressiveList.iter_cow_from_unchecked, ProgressiveList.backing_len,
    utils.Length.as_usize, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at hiter
  rw [bind_eq_ok_iff] at hiter
  obtain ⟨start, hstart, hiter⟩ := hiter
  rw [bind_eq_ok_iff] at hiter
  obtain ⟨treeIter, htree, hiter⟩ := hiter
  simp only [ok.injEq, Prod.mk.injEq] at hiter
  obtain ⟨rfl, rfl⟩ := hiter
  exact ⟨rfl, rfl, rfl⟩

/-- Successful CoW construction retains the exact pending map and starts at
    zero. Its continuation only writes that map back, without representation,
    packing, or generic map-law premises. -/
theorem ProgressiveList.iter_cow_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {cursor : ProgressiveListIterCow T U} {back : ProgressiveListIterCow T U → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow ValueInst mapInst self = ok (cursor, back)) :
    cursor.index = 0#usize ∧ cursor.updates = self.updates ∧
      back = fun replacement => { self with updates := replacement.updates } := by
  unfold ProgressiveList.iter_cow at hiter
  rw [bind_eq_ok_iff] at hiter
  obtain ⟨⟨created, createdBack⟩, hcreated, hiter⟩ := hiter
  obtain ⟨hindex, hupdates, rfl⟩ := unchecked_success_state ValueInst mapInst self 0#usize hcreated
  simp! only [ok.injEq, Prod.mk.injEq] at hiter
  obtain ⟨rfl, rfl⟩ := hiter
  exact ⟨hindex, hupdates, rfl⟩

/-- A successful bounded CoW constructor retains its requested start and
    pending map. The exact write-back behavior needs no representation or
    map laws; an error-valued replacement retains the original map. -/
theorem ProgressiveList.iter_cow_from_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {cursor : ProgressiveListIterCow T U}
    {back : core.result.Result (ProgressiveListIterCow T U) error.Error → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (core.result.Result.Ok cursor, back)) :
    cursor.index = index ∧ cursor.updates = self.updates ∧
      (∀ replacement, back (core.result.Result.Ok replacement) = { self with updates := replacement.updates }) ∧
      (∀ err, back (core.result.Result.Err err) = self) := by
  unfold ProgressiveList.iter_cow_from at hiter
  rw [bind_eq_ok_iff] at hiter
  obtain ⟨length, hlength, hiter⟩ := hiter
  split at hiter
  · simp at hiter
  · rw [bind_eq_ok_iff] at hiter
    obtain ⟨⟨created, createdBack⟩, hcreated, hiter⟩ := hiter
    obtain ⟨hindex, hupdates, rfl⟩ := unchecked_success_state ValueInst mapInst self index hcreated
    simp! only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hiter
    obtain ⟨rfl, rfl⟩ := hiter
    refine ⟨hindex, hupdates, ?_, ?_⟩
    · intro replacement
      cases replacement
      rfl
    · intro err
      simp only [hupdates]

/-- Every returned bounds error restores the original list regardless of the
    continuation input. The statement requires no representation or map law. -/
theorem ProgressiveList.iter_cow_from_error_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {err : error.Error}
    {back : core.result.Result (ProgressiveListIterCow T U) error.Error → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (core.result.Result.Err err, back)) :
    ∀ replacement, back replacement = self := by
  rw [((ProgressiveList.iter_cow_from_error_iff ValueInst mapInst self index).mp hiter).2]
  exact fun _ => rfl

/-- Releasing the freshly constructed cursor unchanged restores the entire
    list. No map release law is needed because construction never borrows a
    map entry or materializes a fallback value. -/
theorem ProgressiveList.iter_cow_read_only_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {cursor : ProgressiveListIterCow T U} {back : ProgressiveListIterCow T U → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow ValueInst mapInst self = ok (cursor, back)) :
    back cursor = self := by
  obtain ⟨_, hupdates, rfl⟩ := ProgressiveList.iter_cow_success_state ValueInst mapInst self hiter
  simp only [hupdates]

/-- Unchanged release restores the original list for every returned result,
    including a bounds error. -/
theorem ProgressiveList.iter_cow_from_read_only_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {result : core.result.Result (ProgressiveListIterCow T U) error.Error}
    {back : core.result.Result (ProgressiveListIterCow T U) error.Error → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (result, back)) :
    back result = self := by
  cases result with
  | Err err => exact ProgressiveList.iter_cow_from_error_preserves_self ValueInst mapInst self index hiter _
  | Ok cursor =>
    obtain ⟨_, hupdates, hback, _⟩ := ProgressiveList.iter_cow_from_success_state ValueInst mapInst self index hiter
    simp only [hback, hupdates]

/-- Every constructor continuation preserves the materialized backing
    invariant, even when its cursor has a changed pending map. -/
theorem ProgressiveList.iter_cow_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {factor : Option Std.Usize}
    (hbacking : self.BackingValid factor)
    {cursor : ProgressiveListIterCow T U} {back : ProgressiveListIterCow T U → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow ValueInst mapInst self = ok (cursor, back)) :
    ∀ replacement, (back replacement).BackingValid factor := by
  obtain ⟨_, _, rfl⟩ := ProgressiveList.iter_cow_success_state ValueInst mapInst self hiter
  exact fun _ => hbacking

/-- The bounded constructor preserves backing validity through every returned
    result and every continuation input, with no additional map laws. -/
theorem ProgressiveList.iter_cow_from_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {factor : Option Std.Usize}
    (hbacking : self.BackingValid factor)
    {result : core.result.Result (ProgressiveListIterCow T U) error.Error}
    {back : core.result.Result (ProgressiveListIterCow T U) error.Error → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (result, back)) :
    ∀ replacement, (back replacement).BackingValid factor := by
  cases result with
  | Err err =>
    intro replacement
    rw [ProgressiveList.iter_cow_from_error_preserves_self ValueInst mapInst self index hiter replacement]
    exact hbacking
  | Ok cursor =>
    obtain ⟨_, _, hok, herr⟩ := ProgressiveList.iter_cow_from_success_state ValueInst mapInst self index hiter
    intro replacement
    cases replacement with
    | Ok changed => rw [hok]; exact hbacking
    | Err err => rw [herr]; exact hbacking

end milhouse.progressive_list
