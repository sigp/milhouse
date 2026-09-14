import Tree.BulkUpdate.Slots

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Pending values in binary ranges skipped by actual false answers already
agree with the original slots. The scope records input geometry and selected
range queries, without an update call or assumed result. Missing pending values
impose no condition, and matching redundant updates are allowed. -/
def Tree.BulkSkippedValuesAgree {T U : Type}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) (depth start offset : Nat) : Prop :=
  ∀ lo hi, BulkRangeQueried mapInst updates factor depth (start + offset) lo hi →
    mapInst.has_any_in_range updates lo hi = ok false →
    ∀ (query : Std.Usize) value, lo.val ≤ query.val → query.val < hi.val →
      mapInst.get updates query = ok (some value) →
      self.slot factor depth (query.val - offset) = some value

/-- Excluding all pending values in skipped ranges implies agreement, but
also rules out harmless matching entries that the weaker law permits. -/
theorem Tree.BulkSkippedValuesAgree.of_ranges {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    (self : Tree T) (depth start offset : Nat)
    (hrange : BulkRangeOn (update_map.RangeExcludesValuesAt mapInst updates)
      mapInst updates factor depth (start + offset)) :
    self.BulkSkippedValuesAgree mapInst updates factor depth start offset := by
  intro lo hi hquery hfalse query value hlo hhi hget
  have hnone := hrange lo hi hquery query (some value) hfalse hget hlo hhi
  cases hnone

theorem Tree.BulkSkippedValuesAgree.left_query {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {left right : Tree T} {child start offset : Nat} {lo hi : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hself : (Tree.Node hash left right).BulkSkippedValuesAgree
      mapInst updates factor (child + 1) start offset)
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hlo : lo.val = start + offset) (hhi : hi.val = start + offset + subtreeCapacity factor child)
    (hfalse : mapInst.has_any_in_range updates lo hi = ok false) :
    ∀ (query : Std.Usize) value, lo.val ≤ query.val → query.val < hi.val →
      mapInst.get updates query = ok (some value) →
      left.slot factor child (query.val - offset) = some value := by
  intro query value hqueryLo hqueryHi hget
  have hread := hself lo hi (.left_here hlo hhi) hfalse query value hqueryLo hqueryHi hget
  rwa [Tree.slot_node_left_of_aligned halign (by omega) (by omega)] at hread

theorem Tree.BulkSkippedValuesAgree.right_query {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {left right : Tree T} {child start offset : Nat} {lo hi : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hself : (Tree.Node hash left right).BulkSkippedValuesAgree
      mapInst updates factor (child + 1) start offset)
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hlo : lo.val = start + offset + subtreeCapacity factor child)
    (hhi : hi.val = start + offset + subtreeCapacity factor child + subtreeCapacity factor child)
    (hfalse : mapInst.has_any_in_range updates lo hi = ok false) :
    ∀ (query : Std.Usize) value, lo.val ≤ query.val → query.val < hi.val →
      mapInst.get updates query = ok (some value) →
      right.slot factor child (query.val - offset) = some value := by
  intro query value hqueryLo hqueryHi hget
  have hread := hself lo hi (.right_here hlo hhi) hfalse query value hqueryLo hqueryHi hget
  have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
    simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
  rwa [Tree.slot_node_right_of_aligned halign (by omega) (by omega)] at hread

theorem Tree.BulkSkippedValuesAgree.left {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {left right : Tree T} {child start offset : Nat} {lo hi : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hself : (Tree.Node hash left right).BulkSkippedValuesAgree
      mapInst updates factor (child + 1) start offset)
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hlo : lo.val = start + offset) (hhi : hi.val = start + offset + subtreeCapacity factor child)
    (hselected : mapInst.has_any_in_range updates lo hi = ok true) :
    left.BulkSkippedValuesAgree mapInst updates factor child start offset := by
  intro queryLo queryHi hquery hfalse query value hqueryLo hqueryHi hget
  have hbounds := hquery.bounds
  have hread := hself queryLo queryHi (.left_tail hlo hhi hselected hquery)
    hfalse query value hqueryLo hqueryHi hget
  rwa [Tree.slot_node_left_of_aligned halign (by omega) (by omega)] at hread

theorem Tree.BulkSkippedValuesAgree.right {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {left right : Tree T} {child start offset : Nat} {lo hi : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hself : (Tree.Node hash left right).BulkSkippedValuesAgree
      mapInst updates factor (child + 1) start offset)
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hlo : lo.val = start + offset + subtreeCapacity factor child)
    (hhi : hi.val = start + offset + subtreeCapacity factor child + subtreeCapacity factor child)
    (hselected : mapInst.has_any_in_range updates lo hi = ok true) :
    right.BulkSkippedValuesAgree mapInst updates factor child (start + subtreeCapacity factor child) offset := by
  intro queryLo queryHi hquery hfalse query value hqueryLo hqueryHi hget
  have hbounds := hquery.bounds
  have hquery' : BulkRangeQueried mapInst updates factor child
      (start + offset + subtreeCapacity factor child) queryLo queryHi := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hquery
  have hread := hself queryLo queryHi (.right_tail hlo hhi hselected hquery')
    hfalse query value hqueryLo hqueryHi hget
  have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
    simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
  rwa [Tree.slot_node_right_of_aligned halign (by omega) (by omega)] at hread

/-- Expanding a zero node preserves every original slot, so it preserves the
skipped-value agreement condition as well. No input invariant is required. -/
theorem Tree.BulkSkippedValuesAgree.zero_expand {T U : Type}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (zeroDepth childDepth : Std.Usize) (depth start offset : Nat)
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)) :
    (Tree.Zero zeroDepth : Tree T).BulkSkippedValuesAgree mapInst updates factor (depth + 1) start offset ↔
      (Tree.Node hash (.Zero childDepth) (.Zero childDepth) : Tree T).BulkSkippedValuesAgree
        mapInst updates factor (depth + 1) start offset := by
  simp only [Tree.BulkSkippedValuesAgree, Tree.slot, ite_self]

end milhouse.tree
