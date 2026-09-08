import Tree.Builder
import Tree.Contents
import Tree.Loop

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- The pending forest's materialized values, in stack order. -/
def stackElements {T : Type} (stack : _root_.List (utils.MaybeArced (tree.Tree T))) : _root_.List T :=
  stack.flatMap (fun entry => (maybeArcedTree entry).elements)

/-- Values accumulated by a builder, independent of its shape and counters. -/
def Builder.elements {T : Type} (self : Builder T) : _root_.List T :=
  stackElements self.stack.val

@[simp] theorem stackElements_nil {T : Type} : stackElements (T := T) [] = [] := rfl

@[simp] theorem stackElements_append {T : Type}
    (left right : _root_.List (utils.MaybeArced (tree.Tree T))) :
    stackElements (left ++ right) = stackElements left ++ stackElements right := by
  simp [stackElements]

@[simp] theorem stackElements_singleton {T : Type} (entry : utils.MaybeArced (tree.Tree T)) :
    stackElements [entry] = (maybeArcedTree entry).elements := by
  simp [stackElements]

theorem bind_eq_ok_iff {A B : Type} {x : Result A} {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

theorem vec_push_values {X : Type} {items result : alloc.vec.Vec X} {last : X}
    (hpush : alloc.vec.Vec.push items last = ok result) :
    result.val = items.val ++ [last] := by
  unfold alloc.vec.Vec.push at hpush
  simp at hpush
  grind

theorem vec_pop_some_values {A X : Type} {source rest : alloc.vec.Vec X} {last : X}
    (hpop : alloc.vec.Vec.pop A source = ok (some last, rest)) :
    source.val = rest.val ++ [last] := by
  unfold alloc.vec.Vec.pop at hpop
  split at hpop
  · simp at hpop
  · rename_i head tail hreverse
    simp at hpop
    obtain ⟨rfl, hrest⟩ := hpop
    have hsource : source.val = tail.reverse ++ [head] := by
      calc
        source.val = source.val.reverse.reverse := by simp
        _ = (head :: tail).reverse := by rw [hreverse]
        _ = tail.reverse ++ [head] := by simp
    have hrestValues : tail.reverse = rest.val := congrArg Subtype.val hrest
    rw [hrestValues] at hsource
    exact hsource

theorem vec_pop_none_values {A X : Type} {source rest : alloc.vec.Vec X}
    (hpop : alloc.vec.Vec.pop A source = ok (none, rest)) :
    source.val = [] ∧ rest.val = [] := by
  unfold alloc.vec.Vec.pop at hpop
  split at hpop
  · rename_i hempty
    simp at hpop
    subst rest
    have hsource : source.val = [] := by
      simpa using congrArg _root_.List.reverse hempty
    exact ⟨hsource, hsource⟩
  · simp at hpop

/-- A binary node concatenates its children's materialized sequences. -/
theorem node_unboxed_elements {T : Type} (ValueInst : Value T)
    {left right result : tree.Tree T}
    (hnode : tree.Tree.node_unboxed ValueInst left right = ok result) :
    result.elements = left.elements ++ right.elements := by
  simp [tree.Tree.node_unboxed, alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new] at hnode
  subst result
  rfl

theorem leaf_unboxed_elements {T : Type} (ValueInst : Value T) {value : T} {result : tree.Tree T}
    (hleaf : tree.Tree.leaf_unboxed ValueInst value = ok result) :
    result.elements = [value] := by
  simp [tree.Tree.leaf_unboxed, leaf.Leaf.new, leaf.Leaf.with_hash,
    alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new,
    triomphe.arc.Arc.new] at hleaf
  subst result
  rfl

/-- A packed singleton stores the supplied value without cloning it. -/
theorem packed_single_values {T : Type} (ValueInst : Value T)
    {value : T} {result : packed_leaf.PackedLeaf T}
    (hsingle : packed_leaf.PackedLeaf.single ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst value = ok result) :
    result.values.val = [value] := by
  unfold packed_leaf.PackedLeaf.single at hsingle
  rw [bind_eq_ok_iff] at hsingle
  obtain ⟨factor, _, hsingle⟩ := hsingle
  rw [bind_eq_ok_iff] at hsingle
  obtain ⟨values, hpush, hsingle⟩ := hsingle
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new] at hsingle
  subst result
  simpa [alloc.vec.Vec.with_capacity] using vec_push_values hpush

/-- Successful packed-leaf push appends exactly one value, without a packing
    bound or element-cloning premise. Success already supplies the checks. -/
theorem packed_push_values {T : Type} (ValueInst : Value T)
    {self result : packed_leaf.PackedLeaf T} {value : T}
    (hpush : packed_leaf.PackedLeaf.push ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst self value = ok (core.result.Result.Ok (), result)) :
    result.values.val = self.values.val ++ [value] := by
  unfold packed_leaf.PackedLeaf.push at hpush
  rw [bind_eq_ok_iff] at hpush
  obtain ⟨factor, _, hpush⟩ := hpush
  split at hpush
  · simp at hpush
  · rw [bind_eq_ok_iff] at hpush
    obtain ⟨values, hvalues, hpush⟩ := hpush
    simp at hpush
    subst result
    exact vec_push_values hvalues

/-- A successful new builder contains no values, independently of packing
    laws or the starting level. -/
theorem Builder.new_elements {T : Type} (ValueInst : Value T) (depth level : Std.Usize)
    {self : Builder T}
    (hnew : Builder.new ValueInst depth level = ok (core.result.Result.Ok self)) :
    self.elements = [] := by
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
    rfl

end milhouse.builder
