import Tree.ProgressiveTree.Density

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Every materialized spine layer has a representable binary capacity. The
    terminal zero needs no bound because lookup returns before doing arithmetic. -/
def ProgressiveTree.Fits {T : Type} (factor : Option Std.Usize) :
    ProgressiveTree T → Nat → Prop
  | .ProgressiveZero, _ => True
  | .ProgressiveNode _ _ right, depth =>
    subtreeCapacity factor (2 * depth) < 2 ^ System.Platform.numBits ∧
      right.Fits factor (depth + 1)

theorem subtreeCapacity_mono_depth (factor : Option Std.Usize) {left right : Nat}
    (hle : left ≤ right) : subtreeCapacity factor left ≤ subtreeCapacity factor right := by
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hle)

end milhouse.progressive_tree
