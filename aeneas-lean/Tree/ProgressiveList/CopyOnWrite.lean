import Tree.ProgressiveList.Spine
import Tree.UpdateMap.CopyOnWrite

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
  rw [get_cow_eq] at hcow
  cases hpending : mapInst.get self.updates index with
  | fail e => simp [hpending] at hcow
  | div => simp [hpending] at hcow
  | ok pending =>
    cases pending with
    | some value =>
      simp only [hpending, bind_tc_ok] at hcow
      exact ⟨none, wrapCow_success ValueInst mapInst self index none hcow⟩
    | none =>
      simp only [hpending, bind_tc_ok] at hcow
      cases hfallback : ProgressiveList.backing_get ValueInst mapInst self index with
      | fail e => simp [hfallback] at hcow
      | div => simp [hfallback] at hcow
      | ok fallback =>
        simp only [hfallback, bind_tc_ok] at hcow
        exact ⟨fallback, wrapCow_success ValueInst mapInst self index fallback hcow⟩

private theorem wrapCow_reads {T U : Type} (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (fallback : Option T)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index) :
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
  exact hproject.trans (hreads fallback)

/-- The element carried by the returned handle agrees with `get`, including
    missing indices and failures. Neither lookup clones the element, so no
    element-cloning law is imposed. -/
theorem ProgressiveList.get_cow_read_eq_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index) :
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
      have hread := wrapCow_reads ValueInst mapInst self index none hreads
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
        have hread := wrapCow_reads ValueInst mapInst self index fallback hreads
        simp only [hpending, bind_tc_ok, Option.none_or] at hread ⊢
        convert hread using 1
        cases wrapCow ValueInst mapInst self index fallback with
        | fail e => rfl
        | div => rfl
        | ok result => obtain ⟨handle, back⟩ := result; rfl

/-- Successful copy-on-write access carries the value of the corresponding
    immutable read. This observes the handle's data; the Rust `Deref` bridge
    is a separate extraction obligation. -/
theorem ProgressiveList.get_cow_reads_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ProgressiveList.get ValueInst mapInst self index = ok (handle.map cow.Cow.value) := by
  have hread := ProgressiveList.get_cow_read_eq_get ValueInst mapInst self index hreads
  simpa [hcow] using hread.symm

/-- If immutable lookup succeeds, copy-on-write access succeeds and carries
    the same optional value. No cloning or structural invariant is required. -/
theorem ProgressiveList.get_cow_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    {value : Option T}
    (hget : ProgressiveList.get ValueInst mapInst self index = ok value) :
    ∃ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) ∧
      handle.map cow.Cow.value = value := by
  have hread := ProgressiveList.get_cow_read_eq_get ValueInst mapInst self index hreads
  rw [hget] at hread
  cases hcow : ProgressiveList.get_cow ValueInst mapInst self index with
  | fail e => simp [hcow] at hread
  | div => simp [hcow] at hread
  | ok result =>
    obtain ⟨handle, back⟩ := result
    exact ⟨handle, back, rfl, by simpa [hcow] using hread⟩

/-- Missing immutable lookup gives a missing copy-on-write handle. -/
theorem ProgressiveList.get_cow_none_of_get_none {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok none) :
    ∃ back, ProgressiveList.get_cow ValueInst mapInst self index = ok (none, back) := by
  obtain ⟨handle, back, hcow, hvalue⟩ :=
    ProgressiveList.get_cow_succeeds ValueInst mapInst self index hreads hget
  cases handle with
  | none => exact ⟨back, hcow⟩
  | some handle => simp at hvalue

/-- Releasing a returned handle unchanged preserves the entire list, including
    pending values and maximum-index metadata. It does not materialize a
    fallback value. The map's release law suffices without a lookup law. -/
theorem ProgressiveList.get_cow_read_only_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hpreserves : update_map.GetCowWithValuePreserves mapInst ValueInst.corecloneCloneInst
      self.updates index)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    back handle = self := by
  obtain ⟨fallback, mapBack, hmap, rfl⟩ :=
    ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  simp only [hpreserves fallback handle mapBack hmap]

/-- **Read-only sequence correctness.** A represented list yields exactly the
    indexed optional element in its handle data, and releasing that handle
    unchanged restores the entire list. Bounds follow from representation;
    no element-cloning law or additional tree invariant is needed. -/
theorem ProgressiveList.get_cow_represents_read {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hpreserves : update_map.GetCowWithValuePreserves mapInst ValueInst.corecloneCloneInst
      self.updates index) :
    ∃ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) ∧
      handle.map cow.Cow.value = contents[index.val]? ∧ back handle = self := by
  obtain ⟨handle, back, hcow, hvalue⟩ :=
    ProgressiveList.get_cow_succeeds ValueInst mapInst self index hreads (hrep.2 index)
  exact ⟨handle, back, hcow, hvalue,
    ProgressiveList.get_cow_read_only_preserves_self ValueInst mapInst self index hpreserves hcow⟩

/-- Out-of-bounds copy-on-write access returns no handle and preserves the
    entire list when released. -/
theorem ProgressiveList.get_cow_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hindex : contents.length ≤ index.val)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hpreserves : update_map.GetCowWithValuePreserves mapInst ValueInst.corecloneCloneInst
      self.updates index) :
    ∃ back, ProgressiveList.get_cow ValueInst mapInst self index = ok (none, back) ∧
      back none = self := by
  have hget := hrep.2 index
  rw [_root_.List.getElem?_eq_none_iff.mpr hindex] at hget
  obtain ⟨back, hcow⟩ :=
    ProgressiveList.get_cow_none_of_get_none ValueInst mapInst self index hreads hget
  exact ⟨back, hcow,
    ProgressiveList.get_cow_read_only_preserves_self ValueInst mapInst self index hpreserves hcow⟩

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

end milhouse.progressive_list
