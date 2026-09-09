import Tree.ProgressiveList.CopyOnWrite
import Tree.ProgressiveList.WriteBack
import Tree.UpdateMap.CowWriteBack

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Exact public read criterion after returning a CoW handle. It needs no
filled-entry footprint or write law because every continuation preserves the
backing fields; its returned map alone determines the lookup condition. -/
theorem ProgressiveList.get_after_cow_writeback_eq_iff_lookup {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back)) :
    ProgressiveList.get ValueInst mapInst (back (some changed)) query =
      (if query = index then ok (some replacement) else ProgressiveList.get ValueInst mapInst self query) ↔
      update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
        (mapInst.get (back (some changed)).updates query)
        (if query = index then ok (some replacement) else mapInst.get self.updates query) := by
  obtain ⟨_, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self _ index query replacement

/-- A returned filled CoW entry changes only the borrowed list index. This
frame result needs neither cloning laws nor structural invariants. -/
theorem ProgressiveList.get_after_cow_writeback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    (hwrites : update_map.GetCowWithValueWriteReads mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    ProgressiveList.get ValueInst mapInst (back (some changed)) query =
      if query = index then ok (some replacement) else ProgressiveList.get ValueInst mapInst self query := by
  obtain ⟨fallback, mapBack, hmap, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact (ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self _ index query replacement).mpr
    (hwrites fallback handle mapBack hmap replacement changed hwritten query)

/-- Exact metadata criterion for the full length result after returning a CoW
handle. The backing length is preserved through every continuation, so this
needs no write-footprint, bounds, representation, or successful query law. -/
theorem ProgressiveList.len_after_cow_writeback_eq_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back)) :
    ProgressiveList.len ValueInst mapInst (back (some changed)) =
        ProgressiveList.len ValueInst mapInst self ↔
      utils.MaxIndexResultsAgree self.length
        (mapInst.max_index (back (some changed)).updates) (mapInst.max_index self.updates) := by
  obtain ⟨_, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ProgressiveList.len_with_updates_eq_iff_max_index ValueInst mapInst self _

/-- A filled CoW entry preserves logical length when the relevant maximum
outcomes agree. No exact insertion maximum or separate index bound is needed. -/
theorem ProgressiveList.len_after_cow_writeback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index length : Std.Usize) (replacement : T)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length)
    (hmax : update_map.GetCowWithValueMaxIndexAgrees mapInst ValueInst.corecloneCloneInst
      self.updates index self.length)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    ProgressiveList.len ValueInst mapInst (back (some changed)) = ok length := by
  obtain ⟨fallback, mapBack, hmap, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ((ProgressiveList.len_with_updates_eq_iff_max_index ValueInst mapInst self _).mpr
    (hmax fallback handle mapBack hmap replacement changed hwritten)).trans hlen

/-- Exact sequence criterion for a returned CoW continuation. Lookup and
maximum agreement are jointly necessary and sufficient without a write law
or an assumed filled-entry footprint. -/
theorem ProgressiveList.cow_writeback_represents_set_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back)) :
    (back (some changed)).Represents ValueInst mapInst (contents.set index.val replacement) ↔
      utils.MaxIndexResultsAgree self.length
        (mapInst.max_index (back (some changed)).updates) (mapInst.max_index self.updates) ∧
      self.SetReadsAgree ValueInst mapInst (back (some changed)).updates index replacement := by
  obtain ⟨_, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ProgressiveList.represents_set_with_updates_iff ValueInst mapInst self contents _ index replacement hrep hindex

/-- Returning a filled CoW entry replaces exactly one represented element
and preserves logical length. The input bound is the only sequence premise
beyond representation, and no element-clone identity is needed. -/
theorem ProgressiveList.cow_writeback_represents_set {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    (hwrites : update_map.GetCowWithValueWriteReads mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : update_map.GetCowWithValueMaxIndexAgrees mapInst ValueInst.corecloneCloneInst
      self.updates index self.length)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    (back (some changed)).Represents ValueInst mapInst (contents.set index.val replacement) := by
  apply (ProgressiveList.cow_writeback_represents_set_iff
    ValueInst mapInst self contents index replacement hrep hindex hcow).mpr
  obtain ⟨fallback, mapBack, hmap, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ⟨hmax fallback handle mapBack hmap replacement changed hwritten,
    hwrites fallback handle mapBack hmap replacement changed hwritten⟩

/-- Accessing and consuming any in-bounds CoW handle succeeds, and writing
through the returned reference replaces precisely that element. All handle,
clone, entry-growth, and metadata continuations are composed from actual
calls. Cloning is required only when no pending value already exists; its
result need not equal the old element. Maximum metadata needs only matching
logical extent, and write-back reads need only agreement after the actual
backing fallback. No backing or packing invariant is needed beyond the original
list representation. -/
theorem ProgressiveList.get_cow_into_mut_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hentry : update_map.GetCowWithValueEntryAt mapInst ValueInst.corecloneCloneInst self.updates index)
    (hexisting : update_map.GetCowWithValueExistingMutable mapInst ValueInst.corecloneCloneInst self.updates index)
    (hwrites : update_map.GetCowWithValueWriteReads mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : update_map.GetCowWithValueMaxIndexAgrees mapInst ValueInst.corecloneCloneInst
      self.updates index self.length)
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone contents[index.val] = ok value) :
    ∃ handle listBack value valueBack,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, listBack) ∧
      cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Ok value, valueBack) ∧
      handle.value = contents[index.val] ∧ handle.MaterializedValue ValueInst.corecloneCloneInst value ∧
      ∀ replacement,
        (listBack (some (valueBack (.Ok replacement)))).Represents ValueInst mapInst (contents.set index.val replacement) ∧
        (listBack (some (valueBack (.Ok replacement)))).tree = self.tree ∧
        (listBack (some (valueBack (.Ok replacement)))).length = self.length := by
  have hget : ProgressiveList.get ValueInst mapInst self index = ok (some contents[index.val]) := by
    rw [hrep.2 index]
    simp [hindex]
  obtain ⟨optional, listBack, hcow, hvalue⟩ := ProgressiveList.get_cow_succeeds ValueInst mapInst self index hreads hget
  cases optional with
  | none => simp at hvalue
  | some handle =>
    simp only [Option.map_some, Option.some.injEq] at hvalue
    obtain ⟨fallback, mapBack, hmap, hlistBack⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
    obtain ⟨length, hlen, hlength⟩ := hrep.1
    have hbound : index.val < Std.Usize.max := by scalar_tac
    have hready := (hentry fallback handle mapBack hmap).canMaterialize hbound
    have hclones : handle.NeedsClone = true →
        ∃ value, ValueInst.corecloneCloneInst.clone handle.value = ok value := by
      intro hneeds
      cases hpending : mapInst.get self.updates index with
      | fail e => simp [ProgressiveList.get, hpending] at hget
      | div => simp [ProgressiveList.get, hpending] at hget
      | ok pending =>
        cases pending with
        | none => simpa only [hvalue] using hclone hpending
        | some old =>
          have hmutable := hexisting fallback handle mapBack hmap old hpending
          simp [hmutable] at hneeds
    obtain ⟨value, valueBack, hmut, hinitial, hwritten⟩ :=
      cow.Cow.into_mut_success ValueInst.corecloneCloneInst handle hready hclones
    refine ⟨handle, listBack, value, valueBack, hcow, hmut, hvalue, hinitial, ?_⟩
    intro replacement
    refine ⟨ProgressiveList.cow_writeback_represents_set ValueInst mapInst self contents index replacement
      hrep hindex hwrites hmax hcow (hwritten replacement), ?_, ?_⟩ <;> rw [hlistBack]

end milhouse.progressive_list
