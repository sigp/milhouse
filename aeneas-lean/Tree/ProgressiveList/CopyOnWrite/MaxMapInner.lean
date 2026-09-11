import Tree.ProgressiveList.CopyOnWrite.MaxMap
import Tree.UpdateMap.MaxMap.CowWriteBack

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The actual wrapper derives its selected write-read agreement from the
inner map. All callbacks are returned with their recorded state, so this
transfer imposes no restriction on nested MaxMap wrappers. -/
theorem ProgressiveList.get_cow_max_map_writeReads_of_inner {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (index : Std.Usize)
    (hwrites : ∀ fallback, self.CowFallbackSelected ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index fallback →
      update_map.GetCowWithValueWriteReadsFor mapInst ValueInst.corecloneCloneInst
        self.updates.inner index
        (ProgressiveList.backing_get ValueInst
          (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self) fallback) :
    self.GetCowWriteReads ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index := by
  intro fallback hselected
  exact update_map.MaxMap.get_cow_writeReadsFor mapInst ValueInst.corecloneCloneInst self.updates
    index _ fallback (hwrites fallback hselected)

/-- A returned filled footprint replaces the represented element using
only the selected inner map's write-read law. The Rust wrapper supplies
callback composition and maximum behavior; no clone or metadata law is added. -/
theorem ProgressiveList.cow_writeback_represents_set_max_map_of_inner {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (contents : _root_.List T)
    (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) contents)
    (hindex : index.val < contents.length)
    (hwrites : ∀ fallback, self.CowFallbackSelected ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index fallback →
      update_map.GetCowWithValueWriteReadsFor mapInst ValueInst.corecloneCloneInst
        self.updates.inner index
        (ProgressiveList.backing_get ValueInst
          (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self) fallback)
    {handle changed : cow.Cow T}
    {back : Option (cow.Cow T) → ProgressiveList T (update_map.MaxMap M)}
    (hcow : ProgressiveList.get_cow ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    (back (some changed)).Represents ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) (contents.set index.val replacement) :=
  ProgressiveList.cow_writeback_represents_set_max_map ValueInst mapInst self contents index replacement
    hrep hindex (ProgressiveList.get_cow_max_map_writeReads_of_inner ValueInst mapInst self index hwrites)
    hcow hwritten

/-- Acquire, consume, and replace an in-bounds value through the actual
MaxMap wrapper. All semantic map premises concern only the selected inner
invocation. The wrapper's read, materialization, callback, write-back, and
maximum behavior is proved from source, including nested callbacks.
The clone need only terminate on an immutable returned value; it need not
preserve that value. No intermediate milhouse success is assumed. -/
theorem ProgressiveList.get_cow_into_mut_max_map_spec_of_inner {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) contents)
    (hindex : index.val < contents.length)
    (hreads : ∀ fallback, self.CowFallbackSelected ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index fallback →
      update_map.GetCowWithValueReadsFor mapInst ValueInst.corecloneCloneInst
        self.updates.inner index fallback)
    (hinputs : ∀ fallback, self.CowFallbackSelected ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index fallback →
      update_map.GetCowWithValueMaterializationInputsFor mapInst ValueInst.corecloneCloneInst
        self.updates.inner index fallback)
    (hwrites : ∀ fallback, self.CowFallbackSelected ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index fallback →
      update_map.GetCowWithValueWriteReadsFor mapInst ValueInst.corecloneCloneInst
        self.updates.inner index
        (ProgressiveList.backing_get ValueInst
          (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self) fallback) :
    ∃ handle listBack value valueBack,
      ProgressiveList.get_cow ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst)
        self index = ok (some handle, listBack) ∧
      cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Ok value, valueBack) ∧
      handle.value = contents[index.val] ∧ handle.MaterializedValue ValueInst.corecloneCloneInst value ∧
      ∀ replacement,
        (listBack (some (valueBack (.Ok replacement)))).Represents ValueInst
          (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) (contents.set index.val replacement) ∧
        (listBack (some (valueBack (.Ok replacement)))).tree = self.tree ∧
        (listBack (some (valueBack (.Ok replacement)))).length = self.length := by
  apply ProgressiveList.get_cow_into_mut_max_map_spec ValueInst mapInst self contents index hrep hindex
  · intro fallback hselected
    exact update_map.MaxMap.get_cow_readsFor mapInst ValueInst.corecloneCloneInst self.updates index
      fallback (hreads fallback hselected)
  · intro fallback hselected
    exact update_map.MaxMap.get_cow_materializationInputsFor mapInst ValueInst.corecloneCloneInst
      self.updates index fallback (hinputs fallback hselected)
  · exact ProgressiveList.get_cow_max_map_writeReads_of_inner ValueInst mapInst self index hwrites

end milhouse.progressive_list
