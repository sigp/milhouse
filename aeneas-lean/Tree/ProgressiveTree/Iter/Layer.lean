import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- A dense spine fills the current binary layer up to its capacity and stores
    exactly the excess length in the right suffix. The full-before-nonempty
    density rule supplies both equalities, including empty internal nodes. -/
theorem ProgressiveTree.Dense.split_layer {T : Type} {factor : Option Std.Usize}
    {depth length : Nat} {left : tree.Tree T} {right : ProgressiveTree T}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hdense : (ProgressiveTree.ProgressiveNode hash left right).Dense factor depth length) :
    DenseTree factor left (2 * depth) (min length (subtreeCapacity factor (2 * depth))) ∧
      right.Dense factor (depth + 1) (length - subtreeCapacity factor (2 * depth)) := by
  cases hdense with
  | @node depth leftLength rightLength left right hash hleft hright hfull =>
    have hbound := hleft.length_le_capacity
    have hleftLength : min (leftLength + rightLength) (subtreeCapacity factor (2 * depth)) = leftLength := by
      by_cases hz : rightLength = 0
      · simpa [hz] using min_eq_left hbound
      · have := hfull (by omega)
        omega
    have hrightLength : leftLength + rightLength - subtreeCapacity factor (2 * depth) = rightLength := by
      by_cases hz : rightLength = 0
      · omega
      · have := hfull (by omega)
        omega
    rw [hleftLength, hrightLength]
    exact ⟨hleft, hright⟩

/-- Removing one binary layer preserves the remaining-global-length equation
    for the progressive suffix, even after the logical end has been reached. -/
theorem ProgressiveTree.Dense.right_remainder {T : Type} {factor : Option Std.Usize}
    {depth length : Nat} {left : tree.Tree T} {right : ProgressiveTree T}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hdense : (ProgressiveTree.ProgressiveNode hash left right).Dense factor depth
      (length - progressiveCapacity factor depth)) :
    right.Dense factor (depth + 1) (length - progressiveCapacity factor (depth + 1)) := by
  simpa only [progressiveCapacity_succ, Nat.sub_sub] using hdense.split_layer.2

end milhouse.progressive_tree
