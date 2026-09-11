import Tree.ProgressiveList.Rebase.State
import Tree.ProgressiveTree.Rebase.SelectedContents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful in-place rebasing preserves the exact materialized backing
contents under the selected semantic laws. No layout, geometry, accurate
length, pending-map, or clone law is needed for this content result. -/
theorem ProgressiveList.rebase_on_preserves_backing_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.tree.elements = self.tree.elements := by
  obtain ⟨newTree, htree, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  exact progressive_tree.ProgressiveTree.rebase_on_preserves_contents_of_inputs ValueInst hcontent htree

/-- Nonmutating rebasing preserves materialized backing contents under the
same selected semantic law. Its actual clone and tree calls are recovered
from success; no pending-map clone-preservation law is needed here. -/
theorem ProgressiveList.rebase_preserves_backing_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.tree.elements = self.tree.elements := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  exact ProgressiveList.rebase_on_preserves_backing_contents ValueInst mapInst
    { self with updates } base hcontent hrebased

end milhouse.progressive_list
