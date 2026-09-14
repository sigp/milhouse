import Tree.ProgressiveList.Rebase.State
import Tree.ProgressiveTree.Rebase.Density

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- In-place rebasing preserves the complete backing traversal invariant.
    The base needs an accurate dense backing length; its pending map and
    capacity bounds are irrelevant. No clone, equality, or hash law is needed
    for this structural result. -/
theorem ProgressiveList.rebase_on_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base =
      ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  obtain ⟨tree, htree, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  exact progressive_tree.ProgressiveTree.rebase_on_preserves_backing ValueInst hlayout
    hbacking.1 hbase hbacking.2 htree

/-- Nonmutating rebasing preserves backing validity under the same premises.
    Cloning the pending map cannot affect the materialized backing invariant,
    so no law about that clone is required. -/
theorem ProgressiveList.rebase_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (core.result.Result.Ok result)) :
    result.BackingValid factor := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  exact ProgressiveList.rebase_on_preserves_backing ValueInst mapInst cloned base hlayout
    (ProgressiveList.clone_preserves_backing ValueInst mapInst self hbacking hcloned) hbase hrebased

end milhouse.progressive_list
