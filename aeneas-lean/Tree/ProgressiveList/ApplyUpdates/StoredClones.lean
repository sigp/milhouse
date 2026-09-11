import Tree.ProgressiveList.ApplyUpdates
import Tree.ProgressiveTree.BulkUpdate.StoredClones

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful nonempty application certifies termination of all selected
stored clones. Only layout is assumed: no input representation, backing,
range, maximum, default, clone, or termination law is needed. -/
theorem ProgressiveList.apply_updates_nonempty_stored_clones_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkStoredCloneOn (fun value => ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
        ValueInst mapInst self.updates factor maximum 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, _⟩
  · rw [hempty] at htrue
    cases htrue
  · exact progressive_tree.ProgressiveTree.with_updated_leaves_stored_clones_terminate
      ValueInst mapInst self.updates hlayout hupdate

end milhouse.progressive_list
