import Tree.ProgressiveList.Rebase.State
import Tree.ProgressiveTree.Rebase.SelectedCaches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Cache validity after successful in-place rebasing is equivalent to the
selected input cache law under selected semantic content soundness. No layout,
geometry, accurate-length, query-success, map, or representation law is needed. -/
theorem ProgressiveList.rebase_on_cache_iff_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self base : ProgressiveList T U)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.tree.CachesOn P 0 ↔
      self.tree.RebaseCacheInputs ValueInst P base.tree self.length.val base.length.val 0 := by
  obtain ⟨newTree, htree, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  exact progressive_tree.ProgressiveTree.rebase_on_cache_iff_of_inputs ValueInst P hcontent htree

/-- The same cache criterion holds for nonmutating rebasing. Actual clone
and rebase calls are recovered from success; no clone-preservation law is
required for the backing cache invariant. -/
theorem ProgressiveList.rebase_cache_iff_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self base : ProgressiveList T U)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.tree.CachesOn P 0 ↔
      self.tree.RebaseCacheInputs ValueInst P base.tree self.length.val base.length.val 0 := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  exact ProgressiveList.rebase_on_cache_iff_of_inputs ValueInst mapInst P
    { self with updates } base hcontent hrebased

end milhouse.progressive_list
