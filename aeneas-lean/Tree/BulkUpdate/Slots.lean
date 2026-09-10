import Tree.BulkUpdate.Node
import Tree.BulkUpdate.RangeScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- A query in an aligned node's left window reads its left child. The slot
model needs no shape or density premise for this routing step. -/
theorem Tree.slot_node_left_of_aligned {T : Type} {factor : Option Std.Usize}
    {left right : Tree T} {child start offset query : Nat}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hlo : start + offset ≤ query)
    (hhi : query < start + offset + subtreeCapacity factor child) :
    (Tree.Node hash left right).slot factor (child + 1) (query - offset) =
      left.slot factor child (query - offset) := by
  have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
    simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
  have hmod := mod_eq_sub_of_aligned halign
    (show start ≤ query - offset by omega)
    (show query - offset < start + subtreeCapacity factor (child + 1) by omega)
  have hroute : (query - offset) % subtreeCapacity factor (child + 1) < subtreeCapacity factor child := by
    rw [hmod]
    omega
  change (if _ then _ else _) = _
  rw [if_pos hroute]

/-- A query in an aligned node's right window reads its right child. -/
theorem Tree.slot_node_right_of_aligned {T : Type} {factor : Option Std.Usize}
    {left right : Tree T} {child start offset query : Nat}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (halign : start % subtreeCapacity factor (child + 1) = 0)
    (hlo : start + offset + subtreeCapacity factor child ≤ query)
    (hhi : query < start + offset + subtreeCapacity factor (child + 1)) :
    (Tree.Node hash left right).slot factor (child + 1) (query - offset) =
      right.slot factor child (query - offset) := by
  have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
    simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
  have hmod := mod_eq_sub_of_aligned halign
    (show start ≤ query - offset by omega)
    (show query - offset < start + subtreeCapacity factor (child + 1) by omega)
  have hroute : ¬ (query - offset) % subtreeCapacity factor (child + 1) < subtreeCapacity factor child := by
    rw [hmod]
    omega
  change (if _ then _ else _) = _
  rw [if_neg hroute]

end milhouse.tree
