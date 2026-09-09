import Tree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- A value law restricted to the clone inputs of a binary bulk update.
At depth zero, packed storage is copied and pending values in the leaf window
are cloned. At a node, only children selected by a successful positive range
query need the law. Zero expansion contributes no stored values. This is a
predicate on input data and external map observations, independent of the
bulk-update computation and its result. It can express clone termination or
value preservation without a law for every value of the element type. -/
def Tree.BulkCloneOn {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) : (depth start : Nat) → Prop
  | 0, start =>
    (match self with
      | .PackedLeaf leaf => ∀ value ∈ leaf.values.val, P value
      | _ => True) ∧
    ∀ (query : Std.Usize) value, start ≤ query.val → query.val < start + leafCapacity factor →
      mapInst.get updates query = ok (some value) → P value
  | depth + 1, start =>
    let (left, right) := match self with
      | .Node _ left right => (left, right)
      | _ => (.Zero 0#usize, .Zero 0#usize)
    (∀ (lo hi : Std.Usize), lo.val = start → hi.val = start + subtreeCapacity factor depth →
      mapInst.has_any_in_range updates lo hi = ok true →
      left.BulkCloneOn P mapInst updates factor depth start) ∧
    (∀ (lo hi : Std.Usize), lo.val = start + subtreeCapacity factor depth →
      hi.val = start + subtreeCapacity factor depth + subtreeCapacity factor depth →
      mapInst.has_any_in_range updates lo hi = ok true →
      right.BulkCloneOn P mapInst updates factor depth (start + subtreeCapacity factor depth))

/-- A global value law specializes to the selected clone inputs. This keeps
older callers usable while recursive specifications adopt the narrower law. -/
theorem Tree.BulkCloneOn.of_all {T U : Type} {P : T → Prop}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (hP : ∀ value, P value) (self : Tree T) (depth start : Nat) :
    self.BulkCloneOn P mapInst updates factor depth start := by
  induction depth generalizing self start with
  | zero =>
    constructor
    · cases self <;> simp_all
    · intro query value _ _ _
      exact hP value
  | succ depth ih =>
    cases self <;> simp only [Tree.BulkCloneOn] <;>
      constructor <;> intro lo hi _ _ _ <;> apply ih

/-- A zero tree has no stored clone inputs, independently of the depth tag
in its Rust representation. The traversal depth determines its windows. -/
theorem Tree.BulkCloneOn.zero_congr {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (first second : Std.Usize) (depth start : Nat) :
    (Tree.Zero first : Tree T).BulkCloneOn P mapInst updates factor depth start ↔
      (Tree.Zero second : Tree T).BulkCloneOn P mapInst updates factor depth start := by
  cases depth <;> rfl

/-- Expanding a zero tree into two zero children preserves the selected
clone-input law. No new value or clone requirement is introduced. -/
theorem Tree.BulkCloneOn.zero_expand {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (zeroDepth childDepth : Std.Usize) (depth start : Nat)
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)) :
    (Tree.Zero zeroDepth : Tree T).BulkCloneOn P mapInst updates factor (depth + 1) start ↔
      (Tree.Node hash (.Zero childDepth) (.Zero childDepth) : Tree T).BulkCloneOn
        P mapInst updates factor (depth + 1) start := by
  simp only [Tree.BulkCloneOn,
    Tree.BulkCloneOn.zero_congr P mapInst updates factor 0#usize childDepth]

end milhouse.tree
