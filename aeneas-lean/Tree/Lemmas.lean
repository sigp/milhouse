-- First lemmas about the extracted tree functions.
import Tree.Funs
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 1000000

open milhouse

namespace milhouse.tree

/-- `get_recursive` on a `Zero` (all-default) subtree returns `none`,
    at any index and depth. -/
theorem get_recursive_zero {T : Type} (ValueInst : Value T)
    (d index depth packing_depth : Std.Usize) :
    Tree.get_recursive ValueInst (Tree.Zero d) index depth packing_depth =
      ok none := by
  unfold Tree.get_recursive
  simp

/-- `get_recursive` on a `Leaf` at depth 0 returns the leaf's value
    (the `Arc` model makes `deref` the identity). -/
theorem get_recursive_leaf {T : Type} (ValueInst : Value T)
    (l : leaf.Leaf T) (index packing_depth : Std.Usize) :
    Tree.get_recursive ValueInst (Tree.Leaf l) index 0#usize packing_depth =
      ok (some l.value) := by
  unfold Tree.get_recursive
  simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]

/-- Roundtrip at depth 0: updating a `Leaf` with `with_updated_leaf`
    succeeds, and `get_recursive` on the result returns the new value —
    at any read index. -/
theorem get_recursive_with_updated_leaf_zero_depth {T : Type}
    (ValueInst : Value T) (l : leaf.Leaf T)
    (index index' packing_depth : Std.Usize) (new_value : T) :
    ∃ t, Tree.with_updated_leaf ValueInst (Tree.Leaf l) index new_value
           0#usize = ok (core.result.Result.Ok t) ∧
         Tree.get_recursive ValueInst t index' 0#usize packing_depth =
           ok (some new_value) := by
  unfold Tree.with_updated_leaf
  simp only [Tree.leaf, leaf.Leaf.new, leaf.Leaf.with_hash,
    alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
  exact ⟨_, rfl, get_recursive_leaf ValueInst _ index' packing_depth⟩

end milhouse.tree
