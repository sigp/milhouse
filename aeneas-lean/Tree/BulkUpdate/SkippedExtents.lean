import Tree.BulkUpdate.Skipped
import Tree.BulkUpdate.Density
import Tree.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- A skipped binary interval keeps its occupied extent when every pending
value there agrees with the original dense slots. Otherwise an extension value
would have to equal a missing slot. Only the input tree and local extension
conditions are used; no successful update, clone, or range-value law is assumed. -/
theorem Tree.BulkSkippedValuesAgree.empty_length {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {self : Tree T} {depth prefix1 offset oldEnd newEnd : Nat} {lo hi : Std.Usize}
    (hagreement : self.BulkSkippedValuesAgree mapInst updates factor depth prefix1 offset)
    (hdense : DenseTree factor self depth
      (min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth)))
    (halign : prefix1 % subtreeCapacity factor depth = 0)
    (hmono : min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth) ≤
      min (newEnd - (prefix1 + offset)) (subtreeCapacity factor depth))
    (hcomplete : ∀ index,
      min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth) ≤ index →
      index < min (newEnd - (prefix1 + offset)) (subtreeCapacity factor depth) →
      update_map.HasValueAt mapInst updates (prefix1 + offset + index))
    (hquery : BulkRangeQueried mapInst updates factor depth (prefix1 + offset) lo hi)
    (hfalse : mapInst.has_any_in_range updates lo hi = ok false) :
    min (newEnd - lo.val) (hi.val - lo.val) = min (oldEnd - lo.val) (hi.val - lo.val) := by
  have hbounds := hquery.bounds
  by_contra hne
  let index := max (min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth))
    (lo.val - (prefix1 + offset))
  have hold : min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth) ≤ index :=
    Nat.le_max_left _ _
  have hnew : index < min (newEnd - (prefix1 + offset)) (subtreeCapacity factor depth) := by
    dsimp [index]
    omega
  obtain ⟨query, value, hqueryVal, hget⟩ := hcomplete index hold hnew
  have hlo : lo.val ≤ query.val := by dsimp [index] at hqueryVal; omega
  have hhi : query.val < hi.val := by dsimp [index] at hqueryVal; omega
  have hagree := hagreement lo hi hquery hfalse query value hlo hhi hget
  have hread := hdense.slot_eq_elements_mod (query.val - offset)
  have hmod := mod_eq_sub_of_aligned halign
    (show prefix1 ≤ query.val - offset by omega)
    (show query.val - offset < prefix1 + subtreeCapacity factor depth by omega)
  rw [hmod] at hread
  have hnone : self.elements[query.val - offset - prefix1]? = none :=
    _root_.List.getElem?_eq_none (by rw [hdense.elements_length]; omega)
  rw [hnone] at hread
  rw [hread] at hagree
  cases hagree

/-- Skipped-value agreement supplies false-answer extent preservation.
Only selected windows need an independent positive-length condition. -/
theorem Tree.BulkSkippedValuesAgree.preservesExtents {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {self : Tree T} {depth prefix1 offset oldEnd newEnd : Nat}
    (hagreement : self.BulkSkippedValuesAgree mapInst updates factor depth prefix1 offset)
    (hdense : DenseTree factor self depth
      (min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth)))
    (halign : prefix1 % subtreeCapacity factor depth = 0)
    (hmono : min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth) ≤
      min (newEnd - (prefix1 + offset)) (subtreeCapacity factor depth))
    (hcomplete : ∀ index,
      min (oldEnd - (prefix1 + offset)) (subtreeCapacity factor depth) ≤ index →
      index < min (newEnd - (prefix1 + offset)) (subtreeCapacity factor depth) →
      update_map.HasValueAt mapInst updates (prefix1 + offset + index))
    (hselected : BulkRangeOn (update_map.RangeSelectsInsideAt mapInst updates newEnd)
      mapInst updates factor depth (prefix1 + offset)) :
    BulkRangeOn (update_map.RangePreservesExtentAt mapInst updates oldEnd newEnd)
      mapInst updates factor depth (prefix1 + offset) := by
  intro lo hi hquery
  exact ⟨hagreement.empty_length hdense halign hmono hcomplete hquery, hselected lo hi hquery⟩

/-- Binary density under the same skipped-value agreement used for contents.
Selected windows need only start inside the final prefix; no positive pending
witness or false-answer exclusion law is required. -/
theorem Tree.with_updated_leaves_capacity_dense_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {prefix1 offset depth : Std.Usize} {oldEnd newEnd : Nat}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hagreement : before.BulkSkippedValuesAgree mapInst updates factor depth.val prefix1.val offset.val)
    (hselected : BulkRangeOn (update_map.RangeSelectsInsideAt mapInst updates newEnd)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val
      (min (oldEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val)))
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val)
      (min (oldEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val))
      (min (newEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val)))
    (hpos : prefix1.val + offset.val < newEnd)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    subtreeCapacity factor depth.val < 2 ^ System.Platform.numBits ∧
      DenseTree factor after depth.val
        (min (newEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val)) := by
  exact Tree.with_updated_leaves_capacity_dense_of_range_extents ValueInst mapInst updates hlayout
    (hagreement.preservesExtents hdense halign hwindow.length_mono hwindow.extension_complete hselected)
    hdense halign hoffset hwindow hpos hupdate

end milhouse.tree
