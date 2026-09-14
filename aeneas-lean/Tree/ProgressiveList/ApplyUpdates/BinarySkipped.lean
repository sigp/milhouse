import Tree.ProgressiveList.ApplyUpdates
import Tree.ProgressiveList.Backing
import Tree.ProgressiveTree.BulkUpdate.BinarySkipped

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful nonempty application with dense, exactly materialized contents
forces pending values skipped inside selected binary layers to agree with their
original slots. Input representation/backing validity and output density supply
the slot relation; no output capacity, range, maximum, default, clone, or
termination law is assumed. -/
theorem ProgressiveList.apply_updates_nonempty_binary_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result))
    (hdense : result.tree.Dense factor 0 result.length.val)
    (helements : result.tree.elements = contents) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinarySkippedValuesAgree ValueInst mapInst self.updates factor maximum 0#u32 := by
  have hoverlay := hrep.overlay ValueInst mapInst hlayout self contents hbacking.1 hbacking.2
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · apply progressive_tree.ProgressiveTree.with_updated_leaves_binary_skipped_values_agree
      ValueInst mapInst self.updates hlayout hupdate
    intro query pending hget _
    obtain ⟨actual, hactual, hvalues⟩ := hoverlay query
    rw [hget] at hactual
    cases hactual
    simp only [show progressive_tree.progressiveCapacity factor 0 = 0 by
      simp [progressive_tree.progressiveCapacity], Nat.sub_zero]
    rw [hdense.slot_eq_elements, hbacking.1.slot_eq_elements, helements]
    exact hvalues.symm

end milhouse.progressive_list
