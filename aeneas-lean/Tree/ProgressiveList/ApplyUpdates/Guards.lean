import Tree.ProgressiveList.ApplyUpdates
import Tree.ProgressiveTree.BulkUpdate.Guards

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful nonempty application certifies the actual selected binary
missing-update guards. Layout and input shape suffice; no range, maximum,
default, clone, termination, density, or capacity law is assumed. -/
theorem ProgressiveList.apply_updates_nonempty_guards_pass {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hshape : self.tree.Shape factor 0)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, _⟩
  · rw [hempty] at htrue
    cases htrue
  · exact progressive_tree.ProgressiveTree.with_updated_leaves_guards_pass
      ValueInst mapInst self.updates hlayout hshape hupdate

end milhouse.progressive_list
