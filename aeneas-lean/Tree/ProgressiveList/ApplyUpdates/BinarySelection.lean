import Tree.ProgressiveList.ApplyUpdates
import Tree.ProgressiveTree.BulkUpdate.BinarySelection

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful nonempty application with dense output forces every selected
binary window to begin inside the final occupied prefix. No input sequence,
input backing invariant, clone, range-value, capacity, default, or termination
law is required. -/

theorem ProgressiveList.apply_updates_nonempty_binary_selection_of_dense_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result))
    (hdense : result.tree.Dense factor 0 result.length.val) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst self.updates result.length.val)
        ValueInst mapInst self.updates factor maximum 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · exact progressive_tree.ProgressiveTree.with_updated_leaves_binary_selection
      ValueInst mapInst self.updates hlayout hupdate hdense

end milhouse.progressive_list
