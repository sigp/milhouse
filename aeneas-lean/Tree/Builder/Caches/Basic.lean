import Tree.HashCache.Cleared
import Tree.Builder.Contents.Basic
import Tree.PackedLeaf.PushState

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

def stackCachesCleared {T : Type} (stack : _root_.List (utils.MaybeArced (tree.Tree T))) : Prop :=
  ∀ entry ∈ stack, (maybeArcedTree entry).CachesCleared

def Builder.CachesCleared {T : Type} (self : Builder T) : Prop :=
  stackCachesCleared self.stack.val

theorem stackCachesCleared.push {T : Type}
    {stack after : alloc.vec.Vec (utils.MaybeArced (tree.Tree T))} {entry : utils.MaybeArced (tree.Tree T)}
    (hstack : stackCachesCleared stack.val) (hentry : (maybeArcedTree entry).CachesCleared)
    (hpush : alloc.vec.Vec.push stack entry = ok after) : stackCachesCleared after.val := by
  rw [vec_push_values hpush]
  intro candidate hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hstack candidate hmem
  · have heq : candidate = entry := by simpa using hmem
    subst candidate
    exact hentry

theorem stackCachesCleared.pop {T : Type}
    {stack rest : alloc.vec.Vec (utils.MaybeArced (tree.Tree T))} {entry : utils.MaybeArced (tree.Tree T)}
    (hstack : stackCachesCleared stack.val)
    (hpop : alloc.vec.Vec.pop Global stack = ok (some entry, rest)) :
    stackCachesCleared rest.val ∧ (maybeArcedTree entry).CachesCleared := by
  constructor
  · intro candidate hmem
    apply hstack candidate
    rw [vec_pop_some_values hpop]
    exact List.mem_append_left _ hmem
  · apply hstack entry
    rw [vec_pop_some_values hpop]
    simp

theorem node_unboxed_caches_cleared {T : Type} (ValueInst : Value T)
    {left right result : tree.Tree T}
    (hleft : left.CachesCleared) (hright : right.CachesCleared)
    (hnode : tree.Tree.node_unboxed ValueInst left right = ok result) : result.CachesCleared := by
  simp [tree.Tree.node_unboxed, alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new] at hnode
  subst result
  exact ⟨rfl, hleft, hright⟩

theorem leaf_unboxed_caches_cleared {T : Type} (ValueInst : Value T)
    {value : T} {result : tree.Tree T}
    (hleaf : tree.Tree.leaf_unboxed ValueInst value = ok result) : result.CachesCleared := by
  simp [tree.Tree.leaf_unboxed, leaf.Leaf.new, leaf.Leaf.with_hash,
    alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new,
    triomphe.arc.Arc.new] at hleaf
  subst result
  rfl

theorem packed_single_caches_cleared {T : Type} (ValueInst : Value T)
    {value : T} {result : packed_leaf.PackedLeaf T}
    (hsingle : packed_leaf.PackedLeaf.single ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst value = ok result) :
    (tree.Tree.PackedLeaf result).CachesCleared := by
  unfold packed_leaf.PackedLeaf.single at hsingle
  rw [bind_eq_ok_iff] at hsingle
  obtain ⟨factor, _, hsingle⟩ := hsingle
  rw [bind_eq_ok_iff] at hsingle
  obtain ⟨values, _, hsingle⟩ := hsingle
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new] at hsingle
  subst result
  rfl

/-- Every successful fresh builder has an empty cache-free forest, without a
packing-layout or arithmetic premise. -/
theorem Builder.new_caches_cleared {T : Type} (ValueInst : Value T) (depth level : Std.Usize)
    {self : Builder T}
    (hnew : Builder.new ValueInst depth level = ok (.Ok self)) : self.CachesCleared := by
  unfold Builder.new at hnew
  simp only [bind_eq_ok_iff, lift, bind_tc_ok] at hnew
  obtain ⟨packing, _, hnew⟩ := hnew
  obtain ⟨maximum, _, hnew⟩ := hnew
  split at hnew
  · simp at hnew
  · simp only [bind_eq_ok_iff] at hnew
    obtain ⟨sum, _, capacity, _, factor, _, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    simp [Builder.CachesCleared, stackCachesCleared, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]

end milhouse.builder
