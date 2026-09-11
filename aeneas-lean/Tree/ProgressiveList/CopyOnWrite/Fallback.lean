import Tree.ProgressiveList.CopyOnWrite.Acquisition

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful copy-on-write access carries the value of the corresponding
    immutable read. This observes the handle's data; the Rust `Deref` bridge
    is a separate extraction obligation. -/
theorem ProgressiveList.get_cow_reads_get_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetCowReads ValueInst mapInst index)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ProgressiveList.get ValueInst mapInst self index = ok (handle.map cow.Cow.value) := by
  have hread := ProgressiveList.get_cow_read_eq_get_of_fallback ValueInst mapInst self index hreads
  simpa [hcow] using hread.symm

/-- If immutable lookup succeeds, copy-on-write access succeeds and carries
    the same optional value. No cloning or structural invariant is required. -/
theorem ProgressiveList.get_cow_succeeds_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetCowReads ValueInst mapInst index)
    {value : Option T}
    (hget : ProgressiveList.get ValueInst mapInst self index = ok value) :
    ∃ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) ∧
      handle.map cow.Cow.value = value := by
  have hread := ProgressiveList.get_cow_read_eq_get_of_fallback ValueInst mapInst self index hreads
  rw [hget] at hread
  cases hcow : ProgressiveList.get_cow ValueInst mapInst self index with
  | fail e => simp [hcow] at hread
  | div => simp [hcow] at hread
  | ok result =>
    obtain ⟨handle, back⟩ := result
    exact ⟨handle, back, rfl, by simpa [hcow] using hread⟩

/-- Missing immutable lookup gives a missing copy-on-write handle. -/
theorem ProgressiveList.get_cow_none_of_get_none_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetCowReads ValueInst mapInst index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok none) :
    ∃ back, ProgressiveList.get_cow ValueInst mapInst self index = ok (none, back) := by
  obtain ⟨handle, back, hcow, hvalue⟩ :=
    ProgressiveList.get_cow_succeeds_of_fallback ValueInst mapInst self index hreads hget
  cases handle with
  | none => exact ⟨back, hcow⟩
  | some handle => simp at hvalue

/-- Releasing a returned handle unchanged preserves the entire list, including
    pending values and maximum-index metadata. It does not materialize a
    fallback value. The map's release law suffices without a lookup law. -/
theorem ProgressiveList.get_cow_read_only_preserves_self_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hpreserves : self.GetCowPreserves ValueInst mapInst index)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    back handle = self := by
  obtain ⟨fallback, mapBack, hselected, hmap, rfl⟩ :=
    ProgressiveList.get_cow_success_fallback ValueInst mapInst self index hcow
  simp only [hpreserves fallback hselected handle mapBack hmap]

/-- **Read-only sequence correctness.** A represented list yields exactly the
    indexed optional element in its handle data, and releasing that handle
    unchanged restores the entire list. Bounds follow from representation;
    no element-cloning law or additional tree invariant is needed. -/
theorem ProgressiveList.get_cow_represents_read_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : self.GetCowReads ValueInst mapInst index)
    (hpreserves : self.GetCowPreserves ValueInst mapInst index) :
    ∃ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) ∧
      handle.map cow.Cow.value = contents[index.val]? ∧ back handle = self := by
  obtain ⟨handle, back, hcow, hvalue⟩ :=
    ProgressiveList.get_cow_succeeds_of_fallback ValueInst mapInst self index hreads (hrep.2 index)
  exact ⟨handle, back, hcow, hvalue,
    ProgressiveList.get_cow_read_only_preserves_self_of_fallback ValueInst mapInst self index hpreserves hcow⟩

/-- Out-of-bounds copy-on-write access returns no handle and preserves the
    entire list when released. -/
theorem ProgressiveList.get_cow_out_of_bounds_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hindex : contents.length ≤ index.val)
    (hreads : self.GetCowReads ValueInst mapInst index)
    (hpreserves : self.GetCowPreserves ValueInst mapInst index) :
    ∃ back, ProgressiveList.get_cow ValueInst mapInst self index = ok (none, back) ∧
      back none = self := by
  have hget := hrep.2 index
  rw [_root_.List.getElem?_eq_none_iff.mpr hindex] at hget
  obtain ⟨back, hcow⟩ :=
    ProgressiveList.get_cow_none_of_get_none_of_fallback ValueInst mapInst self index hreads hget
  exact ⟨back, hcow,
    ProgressiveList.get_cow_read_only_preserves_self_of_fallback ValueInst mapInst self index hpreserves hcow⟩

end milhouse.progressive_list
