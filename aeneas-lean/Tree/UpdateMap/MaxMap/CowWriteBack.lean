import Tree.UpdateMap.MaxMap.CopyOnWrite
import Tree.UpdateMap.CowMaterialization

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map.MaxMap

/-- Attachment preserves the precise entry and immutable-clone inputs.
The actual inner acquisition supplies these inputs for the outer handle. -/
theorem get_cow_materializationInputsFor {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize)
    (fallback : Option T)
    (hinputs : GetCowWithValueMaterializationInputsFor mapInst cloneInst self.inner index fallback) :
    GetCowWithValueMaterializationInputsFor (Insts.MilhouseUpdate_mapUpdateMap mapInst)
      cloneInst self index fallback := by
  intro handle back hcall
  obtain ⟨original, innerBack, hinner, rfl, _⟩ :=
    get_cow_present_result mapInst cloneInst self index fallback hcall
  obtain ⟨hready, hclone⟩ := hinputs original innerBack hinner
  refine ⟨(cow.Cow.attachIndex_canMaterialize original self.max_index index).mpr hready, ?_⟩
  simpa only [cow.Cow.attachIndex_needsClone, cow.Cow.attachIndex_value] using hclone

/-- The source wrapper returns a complete filled footprint to the inner
map. Its selected lookup-agreement law therefore transfers without assuming
that the original handle's callback is empty or already recorded. -/
theorem get_cow_writeReadsFor {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize)
    (backing : Std.Usize → Result (Option T)) (fallback : Option T)
    (hwrites : GetCowWithValueWriteReadsFor mapInst cloneInst self.inner index backing fallback) :
    GetCowWithValueWriteReadsFor (Insts.MilhouseUpdate_mapUpdateMap mapInst)
      cloneInst self index backing fallback := by
  intro handle back hcall replacement changed hwritten query
  obtain ⟨original, innerBack, hinner, rfl, rfl⟩ :=
    get_cow_present_result mapInst cloneInst self index fallback hcall
  exact hwrites original innerBack hinner replacement
    (original.releaseIndex self.max_index changed).1
    (cow.Cow.releaseIndex_written original self.max_index index replacement hwritten) query

/-- Exact inner insertion and lookup framing transfer to the wrapper,
including every original callback and every supplied fallback. -/
theorem get_cow_writes {T M : Type} (mapInst : UpdateMap M T)
    (cloneInst : core.clone.Clone T) (self : MaxMap M) (index : Std.Usize)
    (hwrites : GetCowWithValueWrites mapInst cloneInst self.inner index) :
    GetCowWithValueWrites (Insts.MilhouseUpdate_mapUpdateMap mapInst) cloneInst self index := by
  intro fallback handle back hcall replacement changed hwritten query
  obtain ⟨original, innerBack, hinner, rfl, rfl⟩ :=
    get_cow_present_result mapInst cloneInst self index fallback hcall
  exact hwrites fallback original innerBack hinner replacement
    (original.releaseIndex self.max_index changed).1
    (cow.Cow.releaseIndex_written original self.max_index index replacement hwritten) query

end milhouse.update_map.MaxMap
