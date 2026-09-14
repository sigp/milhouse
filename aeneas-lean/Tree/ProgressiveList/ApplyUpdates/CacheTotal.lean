import Tree.ProgressiveList.ApplyUpdates.Caches
import Tree.ProgressiveList.ApplyUpdates.Total

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Complete public application preserves the represented sequence, valid
backing, and cache validity, and clears pending updates. The cache conclusion
adds only the input cache invariant to the existing total specification. All
work laws remain conditional on the nonempty branch and scoped to reached
queries and cloned values. -/
theorem ProgressiveList.apply_updates_total_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hcache : self.tree.CachesOn (CacheValidFor reference) 0)
    (hempty : ∃ empty, mapInst.is_empty self.updates = ok empty)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hfits : mapInst.is_empty self.updates = ok false →
      ProgressiveTree.LengthFits factor contents.length)
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
        (∀ query, mapInst.get defaults query = ok none) ∧
        mapInst.max_index defaults = ok none ∧ mapInst.is_empty defaults = ok true) :
    ∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  obtain ⟨result, happly, hresult, hvalid, hpending⟩ := ProgressiveList.apply_updates_total_spec
    ValueInst mapInst self contents hrep hbacking hempty hlayout hclone hqueries hrange
    hmaximum hfits hdefault
  exact ⟨result, happly, hresult, hvalid, hpending,
    ProgressiveList.apply_updates_preserves_valid_caches ValueInst mapInst reference self hcache happly⟩

end milhouse.progressive_list
