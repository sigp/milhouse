import Tree.ProgressiveList.Mutable.State

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Mutable access returns an existing pending value directly; otherwise it
returns the actual clone of the backing value. This equation preserves clone
failure and nonidentity results and requires the map read law only at this
list's actual fallback dictionary and environment. -/
theorem ProgressiveList.get_mut_read_eq_pending_or_clone_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetMutReads ValueInst mapInst index) :
    (do let (value, _) ← ProgressiveList.get_mut ValueInst mapInst self index
        ok value) = (do
      let pending ← mapInst.get self.updates index
      match pending with
      | some value => ok (some value)
      | none => do
        let backing ← ProgressiveList.backing_get ValueInst mapInst self index
        core.option.OptionShared0T.cloned ValueInst.corecloneCloneInst backing) := by
  have hread := hreads
  have hproject :
      (do let (value, _) ← ProgressiveList.get_mut ValueInst mapInst self index
          ok value) = (do
        let (value, _) ← mapInst.get_mut_with
          (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption
            ValueInst mapInst) self.updates index (self.tree, self.length)
        ok value) := by
    unfold ProgressiveList.get_mut
    cases mapInst.get_mut_with
        (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption
          ValueInst mapInst) self.updates index (self.tree, self.length) with
    | fail e => rfl
    | div => rfl
    | ok handle => obtain ⟨value, back⟩ := handle; rfl
  refine hproject.trans (hread.trans ?_)
  simp! only [ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption,
    ProgressiveList.get_mut_fallback_eq]
  rfl

/-- Read agreement with `get` needs identity cloning only for an actual
    backing fallback after a missing pending lookup. Pending values, missing
    backing reads, and failing reads need no cloning premise. -/
theorem ProgressiveList.get_mut_read_eq_get_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hclone : mapInst.get self.updates index = ok none → ∀ value,
      ProgressiveList.backing_get ValueInst mapInst self index = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value) :
    (do let (value, _) ← ProgressiveList.get_mut ValueInst mapInst self index
        ok value) = ProgressiveList.get ValueInst mapInst self index := by
  refine (ProgressiveList.get_mut_read_eq_pending_or_clone_of_fallback
    ValueInst mapInst self index hreads).trans ?_
  unfold ProgressiveList.get
  cases hpending : mapInst.get self.updates index with
  | fail e => rfl
  | div => rfl
  | ok pending =>
    cases pending with
    | some value => rfl
    | none =>
      simp only [bind_tc_ok]
      cases hfallback : ProgressiveList.backing_get ValueInst mapInst self index with
      | fail e => rfl
      | div => rfl
      | ok backing =>
        cases backing with
        | none => rfl
        | some value => simp [core.option.OptionShared0T.cloned, hclone hpending value hfallback]

/-- Mutable access reads the same value as `get`, including `none` at missing
    indices, under the map lookup law and value-preserving element cloning. -/
theorem ProgressiveList.get_mut_reads_get_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hclone : mapInst.get self.updates index = ok none → ∀ value,
      ProgressiveList.backing_get ValueInst mapInst self index = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ProgressiveList.get ValueInst mapInst self index = ok value := by
  have hread := ProgressiveList.get_mut_read_eq_get_of_fallback ValueInst mapInst self index hreads hclone
  simpa [hmut] using hread.symm

/-- Whenever the corresponding immutable read succeeds, mutable access also
    succeeds with the same optional element and a write-back continuation. -/
theorem ProgressiveList.get_mut_succeeds_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hclone : mapInst.get self.updates index = ok none → ∀ value,
      ProgressiveList.backing_get ValueInst mapInst self index = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value)
    {value : Option T}
    (hget : ProgressiveList.get ValueInst mapInst self index = ok value) :
    ∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back) := by
  have hread := ProgressiveList.get_mut_read_eq_get_of_fallback ValueInst mapInst self index hreads hclone
  rw [hget] at hread
  cases hmut : ProgressiveList.get_mut ValueInst mapInst self index with
  | fail e => simp [hmut] at hread
  | div => simp [hmut] at hread
  | ok handle =>
    obtain ⟨found, back⟩ := handle
    simp [hmut] at hread
    subst found
    exact ⟨back, rfl⟩

/-- A missing immutable lookup is also missing under mutable access. There is
    no element to clone, so this result requires no element-cloning law. -/
theorem ProgressiveList.get_mut_none_of_get_none_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok none) :
    ∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (none, back) := by
  have hread := hreads
  unfold ProgressiveList.GetMutReads update_map.GetMutWithReadsAt at hread
  cases hpending : mapInst.get self.updates index with
  | fail e => simp [ProgressiveList.get, hpending] at hget
  | div => simp [ProgressiveList.get, hpending] at hget
  | ok pending =>
    cases pending with
    | some value => simp [ProgressiveList.get, hpending] at hget
    | none =>
      simp only [ProgressiveList.get, hpending, bind_tc_ok] at hget
      have hfallback :
          ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption.call_once
            ValueInst mapInst (self.tree, self.length) index = ok none := by
        rw [ProgressiveList.get_mut_fallback_eq, hget]
        rfl
      simp only [hpending, bind_tc_ok, hfallback] at hread
      cases hmap : mapInst.get_mut_with
          (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption
            ValueInst mapInst) self.updates index (self.tree, self.length) with
      | fail e => simp [hmap] at hread
      | div => simp [hmap] at hread
      | ok handle =>
        obtain ⟨found, mapBack⟩ := handle
        simp [hmap] at hread
        subst found
        exact ⟨fun replacement => { self with updates := mapBack replacement },
          by simp [ProgressiveList.get_mut, hmap]⟩

/-- Writing through a present mutable handle changes only the selected list
    element, including all pending and backing lookups at other indices. -/
theorem ProgressiveList.get_after_get_mut_at_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    (hwrites : self.GetMutWriteReads ValueInst mapInst index)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.get ValueInst mapInst (back (some replacement)) query =
      if query = index then ok (some replacement)
      else ProgressiveList.get ValueInst mapInst self query := by
  obtain ⟨mapBack, hmap, rfl⟩ :=
    ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact (ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self _ index query replacement).mpr
    (hwrites _ _ hmap replacement query)

/-- A mutable write preserves logical length under agreement of the relevant
maximum-query outcomes. Exact insertion metadata and a separate index bound
are unnecessary for this observer result. -/
theorem ProgressiveList.len_after_get_mut_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index length : Std.Usize) (replacement : T)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length)
    (hmax : self.GetMutMaxIndexAgrees ValueInst mapInst index)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.len ValueInst mapInst (back (some replacement)) = ok length := by
  obtain ⟨mapBack, hmap, rfl⟩ :=
    ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact ((ProgressiveList.len_with_updates_eq_iff_max_index ValueInst mapInst self _).mpr
    (hmax _ _ hmap replacement)).trans hlen

/-- **Sequence replacement correctness.** Writing a new value through a
    returned mutable element handle preserves length and every other element.
    The old representation and successful read supply the index bound, so
    callers need no separate bounds or tree invariants. -/
theorem ProgressiveList.get_mut_represents_set_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hwrites : self.GetMutWriteReads ValueInst mapInst index)
    (hmax : self.GetMutMaxIndexAgrees ValueInst mapInst index)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    (back (some replacement)).Represents ValueInst mapInst
      (contents.set index.val replacement) := by
  have hget := hrep.2
  have hindex : index.val < contents.length := by
    by_contra hout
    have hnone : contents[index.val]? = none :=
      _root_.List.getElem?_eq_none_iff.mpr (by omega)
    have hgetnone : ProgressiveList.get ValueInst mapInst self index = ok none := by
      rw [hget index, hnone]
    obtain ⟨missingBack, hnoneMut⟩ :=
      ProgressiveList.get_mut_none_of_get_none_of_fallback ValueInst mapInst self index hreads hgetnone
    rw [hmut] at hnoneMut
    cases hnoneMut
  apply (ProgressiveList.get_mut_represents_set_iff
    ValueInst mapInst self contents index replacement hrep hindex hmut).mpr
  obtain ⟨mapBack, hmap, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact ⟨hmax _ _ hmap replacement, hwrites _ _ hmap replacement⟩

/-- Releasing a missing mutable handle preserves the complete list, under the
    generic map's missing-lookup law. -/
theorem ProgressiveList.get_mut_none_preserves_self_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hmissing : self.GetMutMissing ValueInst mapInst index)
    {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (none, back)) :
    back none = self := by
  obtain ⟨mapBack, hmap, rfl⟩ :=
    ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  simp only [hmissing _ hmap]

/-- Out-of-bounds mutable access successfully returns no element and leaves
    the entire list unchanged. Representation supplies the missing immutable
    read, while map laws supply the corresponding mutable behavior. No element
    cloning law is needed for a missing lookup. -/
theorem ProgressiveList.get_mut_out_of_bounds_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hindex : contents.length ≤ index.val)
    (hreads : self.GetMutReads ValueInst mapInst index)
    (hmissing : self.GetMutMissing ValueInst mapInst index) :
    ∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (none, back) ∧
      back none = self := by
  have hget := hrep.2 index
  rw [_root_.List.getElem?_eq_none_iff.mpr hindex] at hget
  obtain ⟨back, hmut⟩ :=
    ProgressiveList.get_mut_none_of_get_none_of_fallback ValueInst mapInst self index hreads hget
  exact ⟨back, hmut,
    ProgressiveList.get_mut_none_preserves_self_of_fallback ValueInst mapInst self index hmissing hmut⟩

end milhouse.progressive_list
