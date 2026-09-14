import Tree.ProgressiveList.CopyOnWrite.Consuming
import Tree.UpdateMap.MaxMap.CopyOnWrite

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- For an in-bounds access, the actual MaxMap callback preserves every
maximum-query outcome relevant to the current logical length. No map-maximum
law, cache-validity invariant, or CoW success is assumed. -/
theorem ProgressiveList.get_cow_max_map_maxIndexAgrees {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (index length : Std.Usize)
    (hlen : ProgressiveList.len ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self = ok length)
    (hindex : index.val < length.val) :
    self.GetCowMaxIndexAgrees ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index := by
  rw [ProgressiveList.len_eq_updated_length] at hlen
  have hmax := update_map.GetCowWithValueMaxIndex.agrees_of_in_bounds
    (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst)
    ValueInst.corecloneCloneInst self.updates index self.length length
    (update_map.MaxMap.get_cow_maxIndex mapInst ValueInst.corecloneCloneInst self.updates index)
    hlen hindex
  exact fun fallback _ => hmax fallback

/-- A filled CoW footprint at an in-bounds key preserves actual logical
length for MaxMap, independently of inner-map read or write laws. -/
theorem ProgressiveList.len_after_cow_writeback_max_map {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (index length : Std.Usize)
    (replacement : T)
    (hlen : ProgressiveList.len ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self = ok length)
    (hindex : index.val < length.val)
    {handle changed : cow.Cow T}
    {back : Option (cow.Cow T) → ProgressiveList T (update_map.MaxMap M)}
    (hcow : ProgressiveList.get_cow ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    ProgressiveList.len ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst)
      (back (some changed)) = ok length :=
  ProgressiveList.len_after_cow_writeback_of_fallback ValueInst
    (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self index length replacement hlen
    (ProgressiveList.get_cow_max_map_maxIndexAgrees ValueInst mapInst self index length hlen hindex)
    hcow hwritten

/-- MaxMap's source callback discharges the independent maximum-agreement
law in the public replacement theorem. Only the selected read-back agreement
remains as a map law; cloning, packing, and cache invariants are unnecessary. -/
theorem ProgressiveList.cow_writeback_represents_set_max_map {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (contents : _root_.List T)
    (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) contents)
    (hindex : index.val < contents.length)
    (hwrites : self.GetCowWriteReads ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index)
    {handle changed : cow.Cow T}
    {back : Option (cow.Cow T) → ProgressiveList T (update_map.MaxMap M)}
    (hcow : ProgressiveList.get_cow ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    (back (some changed)).Represents ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) (contents.set index.val replacement) := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  exact ProgressiveList.cow_writeback_represents_set_of_fallback ValueInst
    (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst)
    self contents index replacement hrep hindex hwrites
    (ProgressiveList.get_cow_max_map_maxIndexAgrees ValueInst mapInst self index length hlen
      (by simpa only [hlength] using hindex)) hcow hwritten

/-- Acquire, consume, and write back an in-bounds CoW handle through the
actual MaxMap dictionary. Its source callback establishes the required length
behavior internally, so no maximum law is assumed. The selected acquisition,
entry/clone inputs, and read-back laws retain their existing scope. -/
theorem ProgressiveList.get_cow_into_mut_max_map_spec {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) contents)
    (hindex : index.val < contents.length)
    (hreads : self.GetCowReads ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index)
    (hinputs : self.GetCowMaterializationInputs ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index)
    (hwrites : self.GetCowWriteReads ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index) :
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
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  exact ProgressiveList.get_cow_into_mut_spec_of_materialization ValueInst
    (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self contents index
    hrep hindex hreads hinputs hwrites
    (ProgressiveList.get_cow_max_map_maxIndexAgrees ValueInst mapInst self index length hlen
      (by simpa only [hlength] using hindex))

end milhouse.progressive_list
