import Tree.ProgressiveList.ApplyUpdates.Total

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful nonempty application certifies representability of every
occupied final layer. Thus the final-capacity condition in the totality
theorem is necessary, even without clone identity, default-map laws, or a
semantic bound on pending values from the returned maximum. -/
theorem ProgressiveList.length_fits_after_nonempty_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveTree.LengthFits factor contents.length := by
  have hafter := ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
    (fun _ => hlayout) (fun _ => hrange) hrep hbacking happly
  have hfits := hafter.1.lengthFits hafter.2
  rwa [ProgressiveList.backing_length_after_nonempty_apply_updates ValueInst mapInst self contents
    hrep hempty happly] at hfits

/-- Given terminating external calls and coherent reached range answers,
nonempty application succeeds exactly when the occupied final layers fit.
The checked length calculation supplies the maximum's numeric extension bound.
External termination is required only at selected clone inputs and reached
range queries. There is no unused-successor capacity requirement. -/
theorem ProgressiveList.apply_updates_nonempty_success_iff_length_fits {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) ↔ ProgressiveTree.LengthFits factor contents.length := by
  constructor
  · rintro ⟨result, happly⟩
    exact ProgressiveList.length_fits_after_nonempty_apply_updates ValueInst mapInst self contents
      hlayout hrange hrep hbacking hempty happly
  · intro hfits
    obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success ValueInst mapInst
      self contents hlayout hclone hqueries hrange hrep hbacking.1 hfits hempty defaults hdefault
    exact ⟨result, happly⟩

end milhouse.progressive_list
