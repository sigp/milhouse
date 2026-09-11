import Tree.BulkUpdate.SkippedSlots
import Tree.BulkUpdate.RetainedClones

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Correct contents after successful rebuilding force pending values in
skipped binary windows to agree with the original slots. No input shape,
density, capacity, offset alignment, range, clone, or termination law is needed. -/
theorem Tree.with_updated_leaves_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after))
    (hcontents : Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val) :
    before.BulkSkippedValuesAgree mapInst updates factor depth.val prefix1.val offset.val := by
  intro lo hi hquery hfalse query value hlo hhi hget
  have hbounds := hquery.bounds
  have hread := hcontents query (some value) hget (by omega) (by omega)
  have hpreserved := Tree.with_updated_leaves_skipped_slots ValueInst mapInst hlayout
    halign hupdate hquery hfalse hlo hhi
  exact hpreserved.symm.trans hread

/-- Correct binary contents are equivalent to retained/pending clone identity
and agreement in skipped windows. No range-correctness law is assumed in either
direction; matching pending values may be skipped. -/
theorem Tree.with_updated_leaves_contents_iff_clones_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after)) :
    Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val ↔
      before.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        mapInst updates factor depth.val (prefix1.val + offset.val) ∧
      before.BulkSkippedValuesAgree mapInst updates factor depth.val prefix1.val offset.val := by
  constructor
  · intro hcontents
    exact ⟨Tree.with_updated_leaves_retained_clone_identity ValueInst mapInst hlayout
      hshape halign hoffset hupdate hcontents,
      Tree.with_updated_leaves_skipped_values_agree ValueInst mapInst hlayout halign hupdate hcontents⟩
  · rintro ⟨hclone, hskipped⟩
    exact (Tree.with_updated_leaves_capacity_shape_contents_of_skipped ValueInst mapInst updates
      hlayout hclone hskipped hshape halign hoffset hupdate).2.2

end milhouse.tree
