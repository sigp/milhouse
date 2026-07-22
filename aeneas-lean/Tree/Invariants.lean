-- Structural invariants for milhouse trees.
import Tree.Funs
open Aeneas Aeneas.Std Result
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Packing configuration -/

/-- The relationship between the packing operations supplied by `Value T` and
    the layout used by a tree.

    `PackingLayout` deliberately includes the power-of-two law.  The extracted
    trait signatures permit arbitrary packing factors, while tree routing uses
    `packing_depth` bits and therefore relies on
    `packing_factor = 2 ^ packing_depth`. -/
inductive PackingLayout {T : Type} (ValueInst : Value T) :
    Option Std.Usize → Std.Usize → Prop where
  | unpacked
      (factor_eq : utils.opt_packing_factor
        ValueInst.tree_hashTreeHashInst = ok none)
      (depth_eq : utils.opt_packing_depth
        ValueInst.tree_hashTreeHashInst = ok none) :
      PackingLayout ValueInst none 0#usize
  | packed (factor packing_depth : Std.Usize)
      (factor_eq : utils.opt_packing_factor
        ValueInst.tree_hashTreeHashInst = ok (some factor))
      (depth_eq : utils.opt_packing_depth
        ValueInst.tree_hashTreeHashInst = ok (some packing_depth))
      (factor_is_power : factor.val = 2 ^ packing_depth.val) :
      PackingLayout ValueInst (some factor) packing_depth

/-! ## Dense tree shape -/

/-- Capacity of one materialized leaf position. An unpacked leaf contains one
    value; a packed leaf contains up to `factor` values. -/
def leafCapacity : Option Std.Usize → Nat
  | none => 1
  | some factor => factor.val

/-- Capacity represented by a subtree at the given tree depth. The depth here
    excludes the packing depth, matching `Tree.get_recursive` and the cached
    depth in `ListInner`/`VectorInner`. -/
def subtreeCapacity (packing_factor : Option Std.Usize) (depth : Nat) : Nat :=
  leafCapacity packing_factor * 2 ^ depth

/-- A tree containing exactly `len` materialized values as a dense left prefix
    of a subtree at `depth`.

    The indices use `Nat` because depth and length are ghost state. Bridge
    lemmas relate them to the `.val` fields of translated `Usize` values.

    The `node` rule is the key left-density condition: the left child is
    non-empty, and a non-empty right child is permitted only after the left
    child reaches its full capacity. Applied recursively, this means that no
    materialized value occurs after a `Zero` padding region. Hash-cache fields
    are intentionally ignored. -/
inductive DenseTree {T : Type} :
    Option Std.Usize → Tree T → Nat → Nat → Prop where
  | zero (packing_factor : Option Std.Usize) (depth : Std.Usize) :
      DenseTree packing_factor (Tree.Zero depth) depth.val 0
  | leaf (l : leaf.Leaf T) :
      DenseTree none (Tree.Leaf l) 0 1
  | packed (factor : Std.Usize) (pl : packed_leaf.PackedLeaf T)
      (values_nonempty : 0 < pl.values.val.length)
      (values_fit : pl.values.val.length ≤ factor.val) :
      DenseTree (some factor) (Tree.PackedLeaf pl) 0 pl.values.val.length
  | node (packing_factor : Option Std.Usize)
      (rl : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (left right : triomphe.arc.Arc (Tree T))
      (child_depth left_len right_len : Nat)
      (left_dense : DenseTree packing_factor left child_depth left_len)
      (right_dense : DenseTree packing_factor right child_depth right_len)
      (left_nonempty : 0 < left_len)
      (left_full_before_right :
        0 < right_len →
          left_len = subtreeCapacity packing_factor child_depth) :
      DenseTree packing_factor (Tree.Node rl left right) (child_depth + 1)
        (left_len + right_len)

/-! ## Initial preservation lemmas -/

/-- `Tree.zero` constructs the canonical dense tree of length zero. -/
theorem zero_preserves_dense {T : Type} (ValueInst : Value T)
    (packing_factor : Option Std.Usize) (depth : Std.Usize) :
    ∃ tree, Tree.zero ValueInst depth = ok tree ∧
      DenseTree packing_factor tree depth.val 0 := by
  refine ⟨Tree.Zero depth, ?_, DenseTree.zero packing_factor depth⟩
  rfl

end milhouse.tree
