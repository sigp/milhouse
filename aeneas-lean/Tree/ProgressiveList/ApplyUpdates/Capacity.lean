import Tree.ProgressiveList.ApplyUpdates.Total

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A successful nonempty application records the represented merged length
as its backing length. This state fact needs no clone, range, or default-map
laws and includes the actual checked length calculation. -/
theorem ProgressiveList.backing_length_after_nonempty_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) : result.length.val = contents.length := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, hlength, _, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · obtain ⟨observed, hobserved, hcontents⟩ := hrep.1
    rw [ProgressiveList.len_eq_updated_length, hlength] at hobserved
    cases hobserved
    exact hcontents

/-- Successful nonempty application certifies representability of every
occupied final layer. Thus the final-capacity condition in the totality
theorem is necessary, even without clone identity or default-map laws. -/
theorem ProgressiveList.length_fits_after_nonempty_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrange : update_map.RangeReflectsValues mapInst self.updates)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveTree.LengthFits factor contents.length := by
  have hafter := ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
    hlayout hrange hmaximum hrep hbacking happly
  have hfits := hafter.1.lengthFits hafter.2
  rwa [ProgressiveList.backing_length_after_nonempty_apply_updates ValueInst mapInst self contents
    hrep hempty happly] at hfits

/-- Given terminating external calls and coherent range/maximum metadata,
nonempty application succeeds exactly when the occupied final layers fit.
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
    (hrange : update_map.RangeReflectsValues mapInst self.updates)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    (defaults : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok defaults) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) ↔ ProgressiveTree.LengthFits factor contents.length := by
  constructor
  · rintro ⟨result, happly⟩
    exact ProgressiveList.length_fits_after_nonempty_apply_updates ValueInst mapInst self contents
      hlayout hrange hmaximum hrep hbacking hempty happly
  · intro hfits
    obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success ValueInst mapInst
      self contents hlayout hclone hqueries hrange hrep hbacking.1 hfits hempty defaults hdefault
    exact ⟨result, happly⟩

end milhouse.progressive_list
