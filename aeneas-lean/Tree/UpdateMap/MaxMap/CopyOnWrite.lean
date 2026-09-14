import Tree.Cow.Attachment
import Tree.UpdateMap.MaxMap.Operations
import Tree.UpdateMap.CopyOnWrite
import Tree.UpdateMap.CowWriteBack

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map.MaxMap

/-- The wrapper continuation restores the original inner callback and
returns the attached maximum borrow separately. Missing loans preserve the
cache for every continuation input. -/
def cowBack {T M : Type} (self : MaxMap M) (index : Std.Usize)
    (found : Option (cow.Cow T)) (innerBack : Option (cow.Cow T) → M)
    (replacement : Option (cow.Cow T)) : MaxMap M :=
  match found with
  | none => { self with inner := innerBack none }
  | some original =>
    let (handle, state) := original.releaseIndex self.max_index
      (replacement.getD (original.attachIndex self.max_index index))
    { inner := innerBack (some handle), max_index := state }

/-- Exact wrapper execution, including inner failure/divergence and all
continuation inputs. Attachment itself is total and does not clone. -/
theorem get_cow_with_value_eq {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize)
    (fallback : Option T) :
    (Insts.MilhouseUpdate_mapUpdateMap mapInst).get_cow_with_value cloneInst self index fallback = (do
      let (found, innerBack) ← mapInst.get_cow_with_value cloneInst self.inner index fallback
      ok (found.map (fun handle => handle.attachIndex self.max_index index),
        cowBack self index found innerBack)) := by
  change Insts.MilhouseUpdate_mapUpdateMap.get_cow_with_value mapInst cloneInst self index fallback = _
  unfold Insts.MilhouseUpdate_mapUpdateMap.get_cow_with_value
  cases mapInst.get_cow_with_value cloneInst self.inner index fallback with
  | fail e => rfl
  | div => rfl
  | ok result =>
    obtain ⟨found, innerBack⟩ := result
    cases found with
    | none => rfl
    | some original =>
      simp only [bind_tc_ok, cow.Cow.with_max_index_eq]
      apply congrArg ok
      apply Prod.ext
      · rfl
      · funext replacement
        cases replacement <;> rfl

/-- Recover the exact inner invocation and the wrapper's attachment from
successful acquisition, with no assumptions about map semantics. -/
theorem get_cow_result {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize)
    (fallback : Option T) {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → MaxMap M}
    (hcall : (Insts.MilhouseUpdate_mapUpdateMap mapInst).get_cow_with_value
      cloneInst self index fallback = ok (handle, back)) :
    ∃ found innerBack,
      mapInst.get_cow_with_value cloneInst self.inner index fallback = ok (found, innerBack) ∧
      handle = found.map (fun original => original.attachIndex self.max_index index) ∧
      back = cowBack self index found innerBack := by
  rw [get_cow_with_value_eq] at hcall
  cases hinner : mapInst.get_cow_with_value cloneInst self.inner index fallback with
  | fail e => simp [hinner] at hcall
  | div => simp [hinner] at hcall
  | ok result =>
    obtain ⟨found, innerBack⟩ := result
    simp! only [hinner, bind_tc_ok, ok.injEq, Prod.mk.injEq] at hcall
    exact ⟨found, innerBack, rfl, hcall.1.symm, hcall.2.symm⟩

theorem get_cow_present_result {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize)
    (fallback : Option T) {handle : cow.Cow T} {back : Option (cow.Cow T) → MaxMap M}
    (hcall : (Insts.MilhouseUpdate_mapUpdateMap mapInst).get_cow_with_value
      cloneInst self index fallback = ok (some handle, back)) :
    ∃ original innerBack,
      mapInst.get_cow_with_value cloneInst self.inner index fallback = ok (some original, innerBack) ∧
      handle = original.attachIndex self.max_index index ∧
      back = cowBack self index (some original) innerBack := by
  obtain ⟨found, innerBack, hinner, hhandle, hback⟩ :=
    get_cow_result mapInst cloneInst self index fallback hcall
  cases found with
  | none => simp at hhandle
  | some original =>
    exact ⟨original, innerBack, hinner, Option.some.inj hhandle, hback⟩

/-- Attaching wrapper metadata preserves the complete carried-value result. -/
theorem get_cow_read_eq {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize) (fallback : Option T) :
    (do let (handle, _) ← (Insts.MilhouseUpdate_mapUpdateMap mapInst).get_cow_with_value
          cloneInst self index fallback
        ok (handle.map cow.Cow.value)) =
      (do let (handle, _) ← mapInst.get_cow_with_value cloneInst self.inner index fallback
          ok (handle.map cow.Cow.value)) := by
  rw [get_cow_with_value_eq]
  cases mapInst.get_cow_with_value cloneInst self.inner index fallback with
  | fail e => rfl
  | div => rfl
  | ok result =>
    obtain ⟨found, innerBack⟩ := result
    cases found <;> simp [cow.Cow.attachIndex_value]

/-- The inner read law transfers at the actual supplied fallback. -/
theorem get_cow_readsFor {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize) (fallback : Option T)
    (hreads : GetCowWithValueReadsFor mapInst cloneInst self.inner index fallback) :
    GetCowWithValueReadsFor (Insts.MilhouseUpdate_mapUpdateMap mapInst)
      cloneInst self index fallback := by
  unfold GetCowWithValueReadsFor
  rw [get_cow_read_eq]
  exact hreads

/-- Unchanged release preserves the wrapper whenever the actual inner loan
does. No cloning, entry-location, or maximum-query law is imposed. -/
theorem get_cow_preservesFor {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize) (fallback : Option T)
    (hpreserves : GetCowWithValuePreservesFor mapInst cloneInst self.inner index fallback) :
    GetCowWithValuePreservesFor (Insts.MilhouseUpdate_mapUpdateMap mapInst)
      cloneInst self index fallback := by
  intro handle back hcall
  obtain ⟨found, innerBack, hinner, rfl, rfl⟩ :=
    get_cow_result mapInst cloneInst self index fallback hcall
  have hrestore := hpreserves found innerBack hinner
  cases found <;> simp [cowBack, cow.Cow.releaseIndex_attachIndex, hrestore]

/-- Attaching metadata retains the inner entry location. -/
theorem get_cow_entryAtFor {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize) (fallback : Option T)
    (hentry : GetCowWithValueEntryAtFor mapInst cloneInst self.inner index fallback) :
    GetCowWithValueEntryAtFor (Insts.MilhouseUpdate_mapUpdateMap mapInst)
      cloneInst self index fallback := by
  intro handle back hcall
  obtain ⟨original, innerBack, hinner, rfl, _⟩ :=
    get_cow_present_result mapInst cloneInst self index fallback hcall
  exact (cow.Cow.attachIndex_entryAt original self.max_index index index).mpr
    (hentry original innerBack hinner)

/-- Already-pending mutable handles remain mutable after attachment. -/
theorem get_cow_existingMutableFor {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize) (fallback : Option T)
    (hexisting : GetCowWithValueExistingMutableFor mapInst cloneInst self.inner index fallback) :
    GetCowWithValueExistingMutableFor (Insts.MilhouseUpdate_mapUpdateMap mapInst)
      cloneInst self index fallback := by
  intro handle back hcall value hpending
  obtain ⟨original, innerBack, hinner, rfl, _⟩ :=
    get_cow_present_result mapInst cloneInst self index fallback hcall
  rw [cow.Cow.attachIndex_needsClone]
  exact hexisting original innerBack hinner value hpending

/-- The actual wrapper enforces insertion-maximum behavior on every filled
CoW footprint. No law about the inner maximum, reads, callbacks, or metadata
invariant is needed, and no index bound or clone law is assumed. -/
theorem get_cow_maxIndex {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize) :
    GetCowWithValueMaxIndex (Insts.MilhouseUpdate_mapUpdateMap mapInst) cloneInst self index := by
  intro fallback handle back hcall replacement changed hwritten oldMax hmax
  obtain ⟨original, innerBack, _, rfl, rfl⟩ :=
    get_cow_present_result mapInst cloneInst self index fallback hcall
  change Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst self = ok oldMax at hmax
  rw [max_index_eq] at hmax
  have hrecord := cow.Cow.releaseIndex_written_maximum original self.max_index index replacement hwritten
  change Insts.MilhouseUpdate_mapUpdateMap.max_index mapInst
    (cowBack self index (some original) innerBack (some changed)) = _
  rw [max_index_eq]
  change ok (original.releaseIndex self.max_index changed).2.toOption = _
  rw [hrecord, MaxIndexState.recorded_toOption, Result.ok.inj hmax]

end milhouse.update_map.MaxMap
