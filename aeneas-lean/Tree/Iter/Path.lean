import Tree.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.iter

/-- A (possibly empty) prefix of the binary search path for `index`. Nodes
    appear in the same root-to-current order as the Rust traversal stack. -/
inductive Path {T : Type} (packingDepth : Nat) :
    tree.Tree T → Nat → Nat → _root_.List (tree.Tree T) → Prop where
  | nil (root : tree.Tree T) (depth index : Nat) : Path packingDepth root depth index []
  | stop (root : tree.Tree T) (depth index : Nat) : Path packingDepth root depth index [root]
  | left {left right : tree.Tree T} {depth index : Nat} {rest : _root_.List (tree.Tree T)}
      (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hbit : index / 2 ^ (depth + packingDepth) % 2 = 0)
      (tail : Path packingDepth left depth index rest) :
      Path packingDepth (.Node hash left right) (depth + 1) index
        (.Node hash left right :: rest)
  | right {left right : tree.Tree T} {depth index : Nat} {rest : _root_.List (tree.Tree T)}
      (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hbit : index / 2 ^ (depth + packingDepth) % 2 ≠ 0)
      (tail : Path packingDepth right depth index rest) :
      Path packingDepth (.Node hash left right) (depth + 1) index
        (.Node hash left right :: rest)

/-- A search path cannot contain more than one node per binary depth. -/
theorem Path.length_le {T : Type} {packingDepth depth index : Nat}
    {root : tree.Tree T} {stack : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth index stack) : stack.length ≤ depth + 1 := by
  induction h <;> simp_all

/-- Truncating a traversal stack leaves a prefix of the same search path. -/
theorem Path.take {T : Type} {packingDepth depth index : Nat}
    {root : tree.Tree T} {stack : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth index stack) (count : Nat) :
    Path packingDepth root depth index (stack.take count) := by
  induction h generalizing count with
  | nil => simp; exact .nil _ _ _
  | stop =>
    cases count with
    | zero => simp; exact .nil _ _ _
    | succ count => simp; exact .stop _ _ _
  | left hash hbit tail ih =>
    cases count with
    | zero => simp; exact .nil _ _ _
    | succ count => simpa using Path.left hash hbit (ih count)
  | right hash hbit tail ih =>
    cases count with
    | zero => simp; exact .nil _ _ _
    | succ count => simpa using Path.right hash hbit (ih count)

/-- Equality of the high bits at one depth implies equality at every higher
    depth. This is the arithmetic needed when reusing ancestor frames. -/
theorem div_pow_eq_of_div_pow_eq {first second low high : Nat}
    (h : first / 2 ^ low = second / 2 ^ low) (hle : low ≤ high) :
    first / 2 ^ high = second / 2 ^ high := by
  have hhigh : high = low + (high - low) := by omega
  rw [hhigh, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

/-- A saved path is still valid for any index in the same interval as its
    deepest retained frame. No density or machine-arithmetic premise is needed. -/
theorem Path.congr_index {T : Type} {packingDepth depth first second : Nat}
    {root : tree.Tree T} {stack : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth first stack)
    (hhigh : first / 2 ^ (depth + 1 - stack.length + packingDepth) =
      second / 2 ^ (depth + 1 - stack.length + packingDepth)) :
    Path packingDepth root depth second stack := by
  induction h with
  | nil => exact .nil _ _ _
  | stop => exact .stop _ _ _
  | @left left right depth index rest hash hbit tail ih =>
    cases rest with
    | nil => exact .stop _ _ _
    | cons frame rest =>
      have hsame : index / 2 ^ (depth + 1 - (frame :: rest).length + packingDepth) =
          second / 2 ^ (depth + 1 - (frame :: rest).length + packingDepth) := by
        simpa only [_root_.List.length_cons, Nat.add_sub_add_right] using hhigh
      have hroute := div_pow_eq_of_div_pow_eq hsame
        (show depth + 1 - (frame :: rest).length + packingDepth ≤ depth + packingDepth by simp)
      exact .left hash (by rwa [← hroute]) (ih hsame)
  | @right left right depth index rest hash hbit tail ih =>
    cases rest with
    | nil => exact .stop _ _ _
    | cons frame rest =>
      have hsame : index / 2 ^ (depth + 1 - (frame :: rest).length + packingDepth) =
          second / 2 ^ (depth + 1 - (frame :: rest).length + packingDepth) := by
        simpa only [_root_.List.length_cons, Nat.add_sub_add_right] using hhigh
      have hroute := div_pow_eq_of_div_pow_eq hsame
        (show depth + 1 - (frame :: rest).length + packingDepth ≤ depth + packingDepth by simp)
      exact .right hash (by rwa [← hroute]) (ih hsame)

/-- Dropping backtracking frames and changing the index is sound whenever the
    new index still belongs to the interval of the deepest surviving frame. -/
theorem Path.take_congr_index {T : Type} {packingDepth depth first second count : Nat}
    {root : tree.Tree T} {stack : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth first stack)
    (hhigh : first / 2 ^ (depth + 1 - min count stack.length + packingDepth) =
      second / 2 ^ (depth + 1 - min count stack.length + packingDepth)) :
    Path packingDepth root depth second (stack.take count) := by
  apply (h.take count).congr_index
  simpa using hhigh

end milhouse.iter
