import Tree.ProgressiveList.CopyOnWrite.Contracts

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private def wrapCow {T U : Type} (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (fallback : Option T) :
    Result (Option (cow.Cow T) × (Option (cow.Cow T) → ProgressiveList T U)) := do
  let (handle, mapBack) ← mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback
  ok (handle, fun replacement => { self with updates := mapBack replacement })

private theorem get_cow_eq {T U : Type} (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) :
    ProgressiveList.get_cow ValueInst mapInst self index = (do
      let pending ← mapInst.get self.updates index
      match pending with
      | some _ => wrapCow ValueInst mapInst self index none
      | none => do
        let fallback ← ProgressiveList.backing_get ValueInst mapInst self index
        wrapCow ValueInst mapInst self index fallback) := by
  unfold ProgressiveList.get_cow
  cases hpending : mapInst.get self.updates index with
  | fail e => simp
  | div => simp
  | ok pending =>
    cases pending <;> simp [core.option.Option.is_some, wrapCow,
      ProgressiveList.backing_get, ProgressiveList.backing_len, utils.Length.as_usize]

private theorem wrapCow_success {T U : Type} (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (fallback : Option T)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hwrap : wrapCow ValueInst mapInst self index fallback = ok (handle, back)) :
    ∃ mapBack,
      mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback =
        ok (handle, mapBack) ∧
      back = fun replacement => { self with updates := mapBack replacement } := by
  unfold wrapCow at hwrap
  cases hmap : mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback with
  | fail e => simp [hmap] at hwrap
  | div => simp [hmap] at hwrap
  | ok result =>
    obtain ⟨found, mapBack⟩ := result
    simp [hmap] at hwrap
    obtain ⟨rfl, hback⟩ := hwrap
    exact ⟨mapBack, rfl, hback.symm⟩

/-- Successful acquisition identifies the fallback selected by the input
lookups, the actual map call, and its continuation. No map, clone, or tree
law is needed to recover this selection evidence. -/
theorem ProgressiveList.get_cow_success_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ∃ fallback mapBack,
      self.CowFallbackSelected ValueInst mapInst index fallback ∧
      mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback =
        ok (handle, mapBack) ∧
      back = fun replacement => { self with updates := mapBack replacement } := by
  rw [get_cow_eq] at hcow
  cases hpending : mapInst.get self.updates index with
  | fail e => simp [hpending] at hcow
  | div => simp [hpending] at hcow
  | ok pending =>
    cases pending with
    | some value =>
      simp only [hpending, bind_tc_ok] at hcow
      obtain ⟨mapBack, hmap, hback⟩ := wrapCow_success ValueInst mapInst self index none hcow
      exact ⟨none, mapBack, Or.inl ⟨value, hpending, rfl⟩, hmap, hback⟩
    | none =>
      simp only [hpending, bind_tc_ok] at hcow
      cases hfallback : ProgressiveList.backing_get ValueInst mapInst self index with
      | fail e => simp [hfallback] at hcow
      | div => simp [hfallback] at hcow
      | ok fallback =>
        simp only [hfallback, bind_tc_ok] at hcow
        obtain ⟨mapBack, hmap, hback⟩ := wrapCow_success ValueInst mapInst self index fallback hcow
        exact ⟨fallback, mapBack, Or.inr ⟨hpending, hfallback⟩, hmap, hback⟩

/-- Successful copy-on-write access uses the map's returned handle and writes
    back only the update-map field. This exact state result requires no map
    laws, value-cloning law, or tree invariant. -/
theorem ProgressiveList.get_cow_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ∃ fallback mapBack,
      mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback =
        ok (handle, mapBack) ∧
      back = fun replacement => { self with updates := mapBack replacement } := by
  obtain ⟨fallback, mapBack, _, hmap, hback⟩ :=
    ProgressiveList.get_cow_success_fallback ValueInst mapInst self index hcow
  exact ⟨fallback, mapBack, hmap, hback⟩

/-- Every copy-on-write continuation preserves the backing-spine invariant.
    This structural property needs no map laws and also holds for arbitrary
    replacement handles, independently of the mutation extraction bridge. -/
theorem ProgressiveList.get_cow_preserves_spine {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {factor : Option Std.Usize}
    (hspine : self.SpineValid factor)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ∀ replacement, (back replacement).SpineValid factor := by
  obtain ⟨fallback, mapBack, _, rfl⟩ :=
    ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact fun _ => hspine

private theorem wrapCow_reads {T U : Type} (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (fallback : Option T)
    (hreads : update_map.GetCowWithValueReadsFor mapInst ValueInst.corecloneCloneInst self.updates index fallback) :
    (do let (handle, _) ← wrapCow ValueInst mapInst self index fallback
        ok (handle.map cow.Cow.value)) =
      (do let pending ← mapInst.get self.updates index
          ok (pending.or fallback)) := by
  have hproject :
      (do let (handle, _) ← wrapCow ValueInst mapInst self index fallback
          ok (handle.map cow.Cow.value)) =
      (do let (handle, _) ← mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback
          ok (handle.map cow.Cow.value)) := by
    unfold wrapCow
    cases mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback with
    | fail e => rfl
    | div => rfl
    | ok result => obtain ⟨handle, mapBack⟩ := result; rfl
  exact hproject.trans hreads

/-- The element carried by the returned handle agrees with `get`, including
    missing indices and failures. Neither lookup clones the element, so no
    element-cloning law is imposed. -/
theorem ProgressiveList.get_cow_read_eq_get_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetCowReads ValueInst mapInst index) :
    (do let (handle, _) ← ProgressiveList.get_cow ValueInst mapInst self index
        ok (handle.map cow.Cow.value)) = ProgressiveList.get ValueInst mapInst self index := by
  rw [get_cow_eq]
  unfold ProgressiveList.get
  cases hpending : mapInst.get self.updates index with
  | fail e => simp
  | div => simp
  | ok pending =>
    cases pending with
    | some value =>
      have hread := wrapCow_reads ValueInst mapInst self index none (hreads none (Or.inl ⟨value, hpending, rfl⟩))
      simp only [hpending, bind_tc_ok, Option.or_none] at hread ⊢
      convert hread using 1
      cases wrapCow ValueInst mapInst self index none with
      | fail e => rfl
      | div => rfl
      | ok result => obtain ⟨handle, back⟩ := result; rfl
    | none =>
      cases hfallback : ProgressiveList.backing_get ValueInst mapInst self index with
      | fail e => simp
      | div => simp
      | ok fallback =>
        have hread := wrapCow_reads ValueInst mapInst self index fallback (hreads fallback (Or.inr ⟨hpending, hfallback⟩))
        simp only [hpending, bind_tc_ok, Option.none_or] at hread ⊢
        convert hread using 1
        cases wrapCow ValueInst mapInst self index fallback with
        | fail e => rfl
        | div => rfl
        | ok result => obtain ⟨handle, back⟩ := result; rfl

end milhouse.progressive_list
