import Tree.Cow.Errors
import Tree.ProgressiveList.CopyOnWrite.Fallback
import Tree.UpdateMap.MaxMap.CopyOnWrite

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A Rust-level consuming error restores the entire acquired list under
only its selected unchanged-release law. No representation, bounds, read,
clone, entry, or maximum law is needed. This does not assert panic recovery. -/
theorem ProgressiveList.get_cow_into_mut_error_restores {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hpreserves : self.GetCowPreserves ValueInst mapInst index)
    {handle : cow.Cow T} {listBack : Option (cow.Cow T) → ProgressiveList T U}
    {error : error.Error} {valueBack : core.result.Result T milhouse.error.Error → cow.Cow T}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, listBack))
    (hmut : cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Err error, valueBack)) :
    error = milhouse.error.Error.CowMissingEntry ∧
      ∀ returned, listBack (some (valueBack returned)) = self := by
  obtain ⟨herr, hback⟩ := cow.Cow.into_mut_error_restores ValueInst.corecloneCloneInst handle hmut
  refine ⟨herr, fun returned => ?_⟩
  rw [hback returned]
  exact ProgressiveList.get_cow_read_only_preserves_self_of_fallback
    ValueInst mapInst self index hpreserves hcow

/-- For MaxMap, only the actual inner loan's unchanged-release law is
required. The wrapper's attachment and maximum metadata restore themselves. -/
theorem ProgressiveList.get_cow_into_mut_error_restores_max_map {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (index : Std.Usize)
    (hpreserves : ∀ fallback,
      self.CowFallbackSelected ValueInst
        (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) index fallback →
      update_map.GetCowWithValuePreservesFor mapInst ValueInst.corecloneCloneInst
        self.updates.inner index fallback)
    {handle : cow.Cow T}
    {listBack : Option (cow.Cow T) → ProgressiveList T (update_map.MaxMap M)}
    {error : error.Error} {valueBack : core.result.Result T milhouse.error.Error → cow.Cow T}
    (hcow : ProgressiveList.get_cow ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self index = ok (some handle, listBack))
    (hmut : cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Err error, valueBack)) :
    error = milhouse.error.Error.CowMissingEntry ∧
      ∀ returned, listBack (some (valueBack returned)) = self := by
  apply ProgressiveList.get_cow_into_mut_error_restores ValueInst
    (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self index ?_ hcow hmut
  intro fallback hselected
  exact update_map.MaxMap.get_cow_preservesFor mapInst ValueInst.corecloneCloneInst
    self.updates index fallback (hpreserves fallback hselected)

end milhouse.progressive_list
