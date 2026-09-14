import Tree.ProgressiveTree.Geometry
import Tree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- The binary layer at progressive depth `n` has binary depth `2 * n`.
    No density or machine-word bound is built into this shape invariant. -/
inductive ProgressiveTree.Shape {T : Type} :
    Option Std.Usize → ProgressiveTree T → Nat → Prop where
  | zero (factor : Option Std.Usize) (depth : Nat) : Shape factor .ProgressiveZero depth
  | node {factor : Option Std.Usize} {depth : Nat}
      {left : tree.Tree T} {right : ProgressiveTree T}
      (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hleft : left.Shape factor (2 * depth)) (hright : right.Shape factor (depth + 1)) :
      Shape factor (.ProgressiveNode hash left right) depth

/-- The terminating zero suffix starts at or beyond `length`. This records
    only where the progressive spine ends; binary density is a separate fact. -/
def ProgressiveTree.EndsAfter {T : Type} (factor : Option Std.Usize)
    (self : ProgressiveTree T) (depth length : Nat) : Prop :=
  match self with
  | .ProgressiveZero => length ≤ progressiveCapacity factor depth
  | .ProgressiveNode _ _ right => right.EndsAfter factor (depth + 1) length

theorem ProgressiveTree.EndsAfter.mono {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {depth oldLength newLength : Nat}
    (hends : self.EndsAfter factor depth oldLength) (hle : newLength ≤ oldLength) :
    self.EndsAfter factor depth newLength := by
  induction self generalizing depth with
  | ProgressiveZero => exact le_trans hle hends
  | ProgressiveNode hash left right ih => exact ih hends

/-- Every suffix ends after its own mathematical starting index, including an
    empty suffix. The bound follows from increasing layer capacities. -/
theorem ProgressiveTree.endsAfter_of_le_start {T : Type} (factor : Option Std.Usize)
    (self : ProgressiveTree T) {depth length : Nat}
    (hle : length ≤ progressiveCapacity factor depth) :
    self.EndsAfter factor depth length := by
  induction self generalizing depth with
  | ProgressiveZero => exact hle
  | ProgressiveNode hash left right ih =>
    exact ih (le_trans hle (progressiveCapacity_mono factor (by omega)))

end milhouse.progressive_tree
