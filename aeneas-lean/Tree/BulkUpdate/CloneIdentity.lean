import Tree.BulkUpdate.Contents
import Tree.PackedLeaf.BulkUpdateIdentity

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Correct contents in an aligned node window restrict to its left child.
This is a routing fact, independent of execution and external laws. -/
theorem Tree.BulkContents.node_left {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {left right newLeft newRight : Tree T} {child start offset : Nat}
    {oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hcontents : Tree.BulkContents mapInst updates factor (.Node oldHash left right)
      (.Node newHash newLeft newRight) (child + 1) start offset) :
    Tree.BulkContents mapInst updates factor left newLeft child start offset := by
  intro query pending hget hlo hhi
  have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
    simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
  have h := hcontents query pending hget hlo (by omega)
  have hmod := mod_eq_sub_of_aligned halign
    (show start ≤ query.val - offset by omega)
    (show query.val - offset < start + subtreeCapacity factor (child + 1) by omega)
  have hroute : (query.val - offset) % subtreeCapacity factor (child + 1) <
      subtreeCapacity factor child := by rw [hmod]; omega
  change (if _ then newLeft.slot factor child (query.val - offset) else _) =
    pending.or (if _ then left.slot factor child (query.val - offset) else _) at h
  simpa only [if_pos hroute] using h

/-- Correct contents in an aligned node window restrict to its right child. -/
theorem Tree.BulkContents.node_right {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {left right newLeft newRight : Tree T} {child start offset : Nat}
    {oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hcontents : Tree.BulkContents mapInst updates factor (.Node oldHash left right)
      (.Node newHash newLeft newRight) (child + 1) start offset) :
    Tree.BulkContents mapInst updates factor right newRight child
      (start + subtreeCapacity factor child) offset := by
  intro query pending hget hlo hhi
  have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
    simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
  have h := hcontents query pending hget (by omega) (by omega)
  have hmod := mod_eq_sub_of_aligned halign
    (show start ≤ query.val - offset by omega)
    (show query.val - offset < start + subtreeCapacity factor (child + 1) by omega)
  have hroute : ¬ (query.val - offset) % subtreeCapacity factor (child + 1) <
      subtreeCapacity factor child := by rw [hmod]; omega
  change (if _ then _ else newRight.slot factor child (query.val - offset)) =
    pending.or (if _ then _ else right.slot factor child (query.val - offset)) at h
  simpa only [if_neg hroute] using h

/-- Correct contents at an unpacked terminal force identity of the consumed
pending clone. No property of the previous slot is needed. -/
theorem Tree.BulkContents.leaf_clone_identity {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {cloneInst : core.clone.Clone T}
    {before : Tree T} {after : leaf.Leaf T} {prefix1 offset index : Std.Usize} {value : T}
    (hindex : prefix1 + offset = ok index)
    (hget : mapInst.get updates index = ok (some value))
    (hclone : cloneInst.clone value = ok after.value)
    (hcontents : Tree.BulkContents mapInst updates none before (.Leaf after) 0 prefix1.val offset.val) :
    ∀ (query : Std.Usize) pending, prefix1.val + offset.val ≤ query.val →
      query.val < prefix1.val + offset.val + leafCapacity none →
      mapInst.get updates query = ok (some pending) → cloneInst.clone pending = ok pending := by
  intro query pending hlo hhi hquery
  have hindexVal := usize_add_val hindex
  simp only [leafCapacity] at hhi
  have heq : query = index := by scalar_tac
  subst query
  rw [hget] at hquery
  cases hquery
  have hread := hcontents index (some value) hget (by omega)
    (by simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one]; omega)
  have hvalue : after.value = value := by simpa only [Tree.slot, Option.some_or, Option.some.injEq] using hread
  simpa only [hvalue] using hclone

/-- Correct binary contents at a packed terminal characterize retained and
pending clone identity, using the actual successful packed update. -/
theorem Tree.bulkContents_packed_iff_retained_clones {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {updates : U} {before after : packed_leaf.PackedLeaf T}
    {factor prefix1 offset start : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    (hfactor : ValueInst.tree_hashTreeHashInst.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0) (hoffset : offset.val % factor.val = 0)
    (hstart : prefix1 + offset = ok start)
    (hupdate : packed_leaf.PackedLeaf.update ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst mapInst before start hash updates = ok (.Ok after)) :
    Tree.BulkContents mapInst updates (some factor) (.PackedLeaf before) (.PackedLeaf after)
      0 prefix1.val offset.val ↔
    (Tree.PackedLeaf before).BulkRetainedCloneOn
      (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
      mapInst updates (some factor) 0 (prefix1.val + offset.val) := by
  have hstartVal := usize_add_val hstart
  have hstartAlign : start.val % factor.val = 0 := by simp [hstartVal, Nat.add_mod, halign, hoffset]
  have hmod : ∀ (query : Std.Usize), start.val ≤ query.val → query.val < start.val + factor.val →
      (query.val - offset.val) % factor.val = query.val - start.val := by
    intro query hlo hhi
    rw [mod_eq_sub_of_aligned halign (by omega) (by omega)]
    omega
  constructor
  · intro hcontents
    have hpacked := (packed_leaf.PackedLeaf.update_contents_iff_retained_clones
      hfactor hstartAlign hupdate).mp (by
        intro query pending hlo hhi hget
        have hread := hcontents query pending hget (by omega)
          (by simpa only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one, ← hstartVal] using hhi)
        simpa only [Tree.slot, leafCapacity, hmod query hlo hhi] using hread)
    simpa only [Tree.BulkRetainedCloneOn, Tree.BulkCloneScope, leafCapacity, ← hstartVal] using hpacked
  · intro hclone
    exact Tree.bulkContents_of_packed_update ValueInst mapInst
      (by simpa only [hstartVal, PackedRetainedCloneOn, leafCapacity] using hclone.1)
      (by simpa only [hstartVal, leafCapacity] using hclone.2) hfactor halign hoffset hstart hupdate

end milhouse.tree
