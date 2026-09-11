import Tree.BulkUpdate.ActivationNecessary
import Tree.ProgressiveTree.BulkUpdate.Activation
import Tree.ProgressiveTree.BulkUpdate.Visited

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Successful progressive rebuilding supplies every selected layer's start
condition. Only positive binary range answers need pending witnesses; false
progressive answers, clone behavior, and external termination are unconstrained.
Input shape supplies packed-leaf metadata compatibility. -/
theorem ProgressiveTree.with_updated_leaves_recursive_layer_enabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hshape : before.Shape factor depth.val)
    (hrange : before.BulkBinaryRangeOn (update_map.RangeSelectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    before.BulkLayerEnabled ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  obtain ⟨result, hbinary⟩ := hvisit.update_success hupdate
  have hpacked : ∀ leaf, layer = .PackedLeaf leaf → factor ≠ none := by
    intro leaf hleaf
    have hshape := hvisit.shape hshape
    rw [hleaf] at hshape
    generalize binary.val = treeDepth at hshape
    cases hshape
    simp
  have hrange := hrange layer start binary hvisit
  simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
    tree.Tree.with_updated_leaves_enabled ValueInst mapInst hlayout hpacked (by simp)
      (by simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using hrange) hbinary

/-- Public successful rebuilding supplies the selected start conditions for
its actual maximum answer, without a density or successful-subcall premise. -/
theorem ProgressiveTree.with_updated_leaves_layer_enabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T}
    (hshape : before.Shape factor 0)
    (hrange : ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkBinaryRangeOn (update_map.RangeSelectsValuesAt mapInst updates)
        ValueInst mapInst updates factor maximum 0#u32)
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates =
      ok (.Ok after)) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkLayerEnabled ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_layer_enabled ValueInst mapInst updates hlayout
    hshape (hrange maximum hmax) hupdate

end milhouse.progressive_tree
