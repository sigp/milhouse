-- Preservation for the specialized repeated-list constructor.
import Tree.Invariants

open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Repeated layers -/

/-- The at-most-two-entry representation maintained by `repeat_list`.

    A singleton is either one final partial tree or copies of a full tree. A
    split layer consists of copies of a full tree followed by one non-empty
    partial tree. `total` is the logical length represented by the layer. -/
inductive RepeatLayer {T : Type} (packing_factor : Option Std.Usize) :
    Nat → Nat → List (Tree T × Std.Usize) → Prop where
  | single (tree : Tree T) (count : Std.Usize) (depth len total : Nat)
      (dense : DenseTree packing_factor tree depth len)
      (len_pos : 0 < len) (count_pos : 0 < count.val)
      (total_eq : total = len * count.val)
      (one_or_full : count.val = 1 ∨
        len = subtreeCapacity packing_factor depth) :
      RepeatLayer packing_factor depth total [(tree, count)]
  | split (repeated lonely : Tree T) (count : Std.Usize)
      (depth lonely_len total : Nat)
      (repeated_dense : DenseTree packing_factor repeated depth
        (subtreeCapacity packing_factor depth))
      (lonely_dense : DenseTree packing_factor lonely depth lonely_len)
      (count_pos : 0 < count.val) (lonely_pos : 0 < lonely_len)
      (lonely_partial : lonely_len < subtreeCapacity packing_factor depth)
      (total_eq : total =
        subtreeCapacity packing_factor depth * count.val + lonely_len) :
      RepeatLayer packing_factor depth total
        [(repeated, count), (lonely, 1#usize)]

/-- A finalized singleton layer contains a dense tree for its entire logical
    length. -/
theorem RepeatLayer.singleton_dense {T : Type}
    {packing_factor : Option Std.Usize} {depth total : Nat} {tree : Tree T}
    (hlayer : RepeatLayer packing_factor depth total [(tree, 1#usize)]) :
    DenseTree packing_factor tree depth total := by
  cases hlayer with
  | single tree count depth len total hdense _ _ htotal _ =>
    simp at htotal
    simpa [htotal] using hdense

private theorem subtreeCapacity_succ
    (packing_factor : Option Std.Usize) (depth : Nat) :
    subtreeCapacity packing_factor (depth + 1) =
      2 * subtreeCapacity packing_factor depth := by
  simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- Padding a non-empty dense tree on the right preserves its logical length. -/
private theorem DenseTree.pad_right {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T}
    (depth : Std.Usize) {len : Nat}
    (hdense : DenseTree packing_factor tree depth.val len)
    (hlen : 0 < len)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    DenseTree packing_factor (Tree.Node hash tree (Tree.Zero depth))
      (depth.val + 1) len := by
  simpa using DenseTree.node packing_factor hash tree (Tree.Zero depth)
    depth.val len 0 hdense (DenseTree.zero packing_factor depth) hlen (by omega)

/-- Pairing two copies of a full dense tree produces a full parent. -/
private theorem DenseTree.pair_full {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T}
    (depth : Std.Usize)
    (hdense : DenseTree packing_factor tree depth.val
      (subtreeCapacity packing_factor depth.val))
    (hcapacity : 0 < subtreeCapacity packing_factor depth.val)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    DenseTree packing_factor (Tree.Node hash tree tree) (depth.val + 1)
      (subtreeCapacity packing_factor (depth.val + 1)) := by
  have hnode := DenseTree.node packing_factor hash tree tree depth.val
    (subtreeCapacity packing_factor depth.val)
    (subtreeCapacity packing_factor depth.val) hdense hdense hcapacity
    (by intros; rfl)
  simpa [subtreeCapacity_succ, two_mul] using hnode

/-- Appending a non-empty partial dense tree to a full left sibling produces
    the corresponding dense parent. -/
private theorem DenseTree.pair_partial {T : Type}
    {packing_factor : Option Std.Usize} {left right : Tree T}
    (depth : Std.Usize) {right_len : Nat}
    (hleft : DenseTree packing_factor left depth.val
      (subtreeCapacity packing_factor depth.val))
    (hright : DenseTree packing_factor right depth.val right_len)
    (hcapacity : 0 < subtreeCapacity packing_factor depth.val)
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    DenseTree packing_factor (Tree.Node hash left right) (depth.val + 1)
      (subtreeCapacity packing_factor depth.val + right_len) := by
  exact DenseTree.node packing_factor hash left right depth.val
    (subtreeCapacity packing_factor depth.val) right_len hleft hright
    hcapacity (by intros; rfl)

end milhouse.tree
