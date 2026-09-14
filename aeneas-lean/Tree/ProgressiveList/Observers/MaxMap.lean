import Tree.ProgressiveList.Observers
import Tree.UpdateMap.MaxMap.Empty

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- With the actual MaxMap dictionary, pending-update detection depends only
on the inner map's length. The equation includes failure and divergence. -/
theorem ProgressiveList.has_pending_updates_max_map_eq {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) :
    ProgressiveList.has_pending_updates ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self = (do
        let length ← mapInst.len self.updates.inner
        ok (!decide (length = 0#usize))) := by
  unfold ProgressiveList.has_pending_updates
  rw [update_map.MaxMap.is_empty_eq]
  cases mapInst.len self.updates.inner <;> simp

/-- Specializing the generic pending observer to MaxMap removes its separate
emptiness-answer premise: the inner length result determines the answer. -/
theorem ProgressiveList.has_pending_updates_max_map_spec {T M : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap M T)
    (self : ProgressiveList T (update_map.MaxMap M)) (length : Std.Usize)
    (hlen : mapInst.len self.updates.inner = ok length) :
    ProgressiveList.has_pending_updates ValueInst
      (update_map.MaxMap.Insts.MilhouseUpdate_mapUpdateMap mapInst) self =
      ok (!decide (length = 0#usize)) := by
  rw [ProgressiveList.has_pending_updates_max_map_eq, hlen]
  rfl

end milhouse.progressive_list
