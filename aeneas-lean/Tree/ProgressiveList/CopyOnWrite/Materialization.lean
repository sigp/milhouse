import Tree.ProgressiveList.CopyOnWrite.Fallback
import Tree.Cow.ConsumingConditions

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Structural entry readiness and actual clone termination for present
handles returned by the selected map invocation. These input laws impose no
entry-key equality and require a clone only for an immutable handle. They
do not assume success of `Cow.into_mut` or any list write-back behavior. -/
abbrev ProgressiveList.GetCowMaterializationInputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  ∀ fallback, self.CowFallbackSelected ValueInst mapInst index fallback →
    ∀ handle mapBack,
      mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback =
        ok (some handle, mapBack) →
      handle.CanMaterialize ∧
        (handle.NeedsClone = true →
          ∃ value, ValueInst.corecloneCloneInst.clone handle.value = ok value)

/-- Actual acquisition followed by successful consumption supplies all of
the selected map invocation's materialization inputs. No read, location,
clone, representation, or write-back law is assumed. -/
theorem ProgressiveList.get_cow_into_mut_materialization_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {handle : cow.Cow T} {listBack : Option (cow.Cow T) → ProgressiveList T U}
    {value : T} {valueBack : core.result.Result T error.Error → cow.Cow T}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, listBack))
    (hmut : cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Ok value, valueBack)) :
    self.GetCowMaterializationInputs ValueInst mapInst index := by
  intro fallback hselected found mapBack hmap
  have hfound : ProgressiveList.get_cow ValueInst mapInst self index =
      ok (some found, fun replacement => { self with updates := mapBack replacement }) := by
    rw [ProgressiveList.get_cow_eq_of_fallback ValueInst mapInst self index fallback hselected]
    simp only [hmap, bind_tc_ok]
    rfl
  have hsame : handle = found := by
    have heq := hcow.symm.trans hfound
    simp at heq
    exact heq.1
  subst found
  exact (cow.Cow.into_mut_success_iff ValueInst.corecloneCloneInst handle).mp
    ⟨value, valueBack, hmut⟩

/-- With the read law at the selected fallback, acquisition followed by
consumption succeeds exactly when immutable lookup is present and the
returned handles have the structural entry and clone inputs. No representation,
key-location, pending-handle, clone, or write-back laws are assumed upfront. -/
theorem ProgressiveList.get_cow_into_mut_success_iff_of_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : self.GetCowReads ValueInst mapInst index) :
    (∃ handle listBack value valueBack,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, listBack) ∧
      cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Ok value, valueBack)) ↔
    (∃ original, ProgressiveList.get ValueInst mapInst self index = ok (some original)) ∧
      self.GetCowMaterializationInputs ValueInst mapInst index := by
  constructor
  · rintro ⟨handle, listBack, value, valueBack, hcow, hmut⟩
    refine ⟨⟨handle.value, ?_⟩,
      ProgressiveList.get_cow_into_mut_materialization_inputs ValueInst mapInst self index hcow hmut⟩
    exact ProgressiveList.get_cow_reads_get_of_fallback ValueInst mapInst self index hreads hcow
  · rintro ⟨⟨original, hget⟩, hinputs⟩
    obtain ⟨optional, listBack, hcow, hvalue⟩ :=
      ProgressiveList.get_cow_succeeds_of_fallback ValueInst mapInst self index hreads hget
    cases optional with
    | none => simp at hvalue
    | some handle =>
      obtain ⟨fallback, mapBack, hselected, hmap, _⟩ :=
        ProgressiveList.get_cow_success_fallback ValueInst mapInst self index hcow
      obtain ⟨hready, hclone⟩ := hinputs fallback hselected handle mapBack hmap
      obtain ⟨value, valueBack, hmut, _⟩ :=
        cow.Cow.into_mut_success ValueInst.corecloneCloneInst handle hready hclone
      exact ⟨handle, listBack, value, valueBack, hcow, hmut⟩

end milhouse.progressive_list
