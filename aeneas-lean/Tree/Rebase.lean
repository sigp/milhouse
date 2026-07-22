-- Density preservation machinery for structural sharing.
import Tree.Invariants
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-- A tree obtained by choosing corresponding pieces of two trees. This is
    the shape-level effect of `Tree.rebase_on`: cache hashes and ownership may
    change, but a replacement never moves a subtree to a different position. -/
inductive PositionalMix {T : Type} : Tree T → Tree T → Tree T → Prop where
  | orig (orig base : Tree T) : PositionalMix orig base orig
  | base (orig base : Tree T) : PositionalMix orig base base
  | node
      (orig_hash base_hash new_hash :
        alloy_primitives.bits.fixed.FixedBytes 32#usize)
      (orig_left orig_right base_left base_right new_left new_right : Tree T)
      (left_mix : PositionalMix orig_left base_left new_left)
      (right_mix : PositionalMix orig_right base_right new_right) :
      PositionalMix
        (Tree.Node orig_hash orig_left orig_right)
        (Tree.Node base_hash base_left base_right)
        (Tree.Node new_hash new_left new_right)

private theorem dense_split_unique {capacity left₁ right₁ left₂ right₂ : Nat}
    (left₁_bound : left₁ ≤ capacity)
    (left₂_bound : left₂ ≤ capacity)
    (left₁_nonempty : 0 < left₁)
    (left₂_nonempty : 0 < left₂)
    (left₁_full : 0 < right₁ → left₁ = capacity)
    (left₂_full : 0 < right₂ → left₂ = capacity)
    (length_eq : left₁ + right₁ = left₂ + right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  by_cases hright₁ : 0 < right₁ <;>
    by_cases hright₂ : 0 < right₂
  · have hfull₁ := left₁_full hright₁
    have hfull₂ := left₂_full hright₂
    omega
  · have hfull₁ := left₁_full hright₁
    omega
  · have hfull₂ := left₂_full hright₂
    omega
  · omega

private theorem dense_node_inv {T : Type}
    {packing_factor : Option Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    {left right : Tree T} {depth len : Nat}
    (h : DenseTree packing_factor (Tree.Node hash left right) depth len) :
    ∃ child_depth left_len right_len,
      depth = child_depth + 1 ∧ len = left_len + right_len ∧
      DenseTree packing_factor left child_depth left_len ∧
      DenseTree packing_factor right child_depth right_len ∧
      0 < left_len ∧
      (0 < right_len →
        left_len = subtreeCapacity packing_factor child_depth) := by
  cases h with
  | node _ _ _ _ child_depth left_len right_len hleft hright hleftpos hfull =>
    exact ⟨child_depth, left_len, right_len, rfl, rfl, hleft, hright,
      hleftpos, hfull⟩

/-- Mixing corresponding positions of two dense trees with the same logical
    indices produces another dense tree with those indices. -/
theorem PositionalMix.preserves_dense {T : Type}
    {packing_factor : Option Std.Usize} {orig base mixed : Tree T}
    {depth len : Nat}
    (hmix : PositionalMix orig base mixed)
    (horig : DenseTree packing_factor orig depth len)
    (hbase : DenseTree packing_factor base depth len) :
    DenseTree packing_factor mixed depth len := by
  induction hmix generalizing depth len with
  | orig orig base => exact horig
  | base orig base => exact hbase
  | node orig_hash base_hash new_hash orig_left orig_right base_left base_right
      new_left new_right left_mix right_mix ihleft ihright =>
    obtain ⟨orig_child_depth, orig_left_len, orig_right_len,
      horig_depth, horig_len, orig_left_dense, orig_right_dense,
      orig_left_nonempty, orig_left_full⟩ := dense_node_inv horig
    obtain ⟨base_child_depth, base_left_len, base_right_len,
      hbase_depth, hbase_len, base_left_dense, base_right_dense,
      base_left_nonempty, base_left_full⟩ := dense_node_inv hbase
    have hchild_depth : orig_child_depth = base_child_depth := by omega
    subst base_child_depth
    have hsplit := dense_split_unique
      orig_left_dense.length_le_capacity
      base_left_dense.length_le_capacity
      orig_left_nonempty base_left_nonempty orig_left_full base_left_full
      (by omega)
    obtain ⟨hleft_len, hright_len⟩ := hsplit
    subst base_left_len
    subst base_right_len
    rw [horig_depth, horig_len]
    exact DenseTree.node packing_factor new_hash new_left new_right
      orig_child_depth orig_left_len orig_right_len
      (ihleft orig_left_dense base_left_dense)
      (ihright orig_right_dense base_right_dense)
      orig_left_nonempty orig_left_full

/-- The concrete tree denoted by a rebase action: no-op actions retain the
    original, while replacement actions carry their new tree. -/
def applyRebaseAction {T : Type} (orig : Tree T) :
    tree.RebaseAction (Tree T) → Tree T
  | tree.RebaseAction.NotEqualNoop => orig
  | tree.RebaseAction.NotEqualReplace replacement => replacement
  | tree.RebaseAction.EqualNoop => orig
  | tree.RebaseAction.EqualReplace replacement => replacement

/-- Once a rebase action is known to be positional, density follows directly. -/
theorem rebaseAction_preserves_dense {T : Type}
    {packing_factor : Option Std.Usize} {orig base : Tree T}
    {depth len : Nat} {action : tree.RebaseAction (Tree T)}
    (hmix : PositionalMix orig base (applyRebaseAction orig action))
    (horig : DenseTree packing_factor orig depth len)
    (hbase : DenseTree packing_factor base depth len) :
    DenseTree packing_factor (applyRebaseAction orig action) depth len :=
  hmix.preserves_dense horig hbase

end milhouse.tree
