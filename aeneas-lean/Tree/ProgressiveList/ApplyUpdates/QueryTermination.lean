import Tree.ProgressiveList.ApplyUpdates
import Tree.ProgressiveTree.BulkUpdate.QueryTermination

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful nonempty application certifies termination of every scoped
progressive and binary range query. Only layout is assumed, with no input,
clone, map-correctness, default, or external termination law. -/
theorem ProgressiveList.apply_updates_nonempty_queries_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32 := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, _, hupdate, _⟩
  · rw [hempty] at htrue
    cases htrue
  · exact progressive_tree.ProgressiveTree.with_updated_leaves_queries_terminate
      ValueInst mapInst self.updates hlayout hupdate

end milhouse.progressive_list
