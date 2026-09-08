import Tree.Builder.Contents.Basic
import Tree.ProgressiveTree.Density

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- The spine obtained by prepending the supplied binary subtrees in order.
    New nodes have the same empty hash cache as the extracted constructor. -/
def ProgressiveTree.ofSubtrees {T : Type} (subtrees : _root_.List (tree.Tree T))
    (suffix : ProgressiveTree T) : ProgressiveTree T :=
  subtrees.foldr (fun left right => .ProgressiveNode (Array.repeat 32#usize 0#u8) left right) suffix

theorem ProgressiveTree.ofSubtrees_elements {T : Type}
    (subtrees : _root_.List (tree.Tree T)) (suffix : ProgressiveTree T) :
    (ProgressiveTree.ofSubtrees subtrees suffix).elements =
      subtrees.flatMap tree.Tree.elements ++ suffix.elements := by
  induction subtrees with
  | nil => rfl
  | cons head tail ih =>
    simp only [ProgressiveTree.ofSubtrees, _root_.List.foldr_cons,
      ProgressiveTree.elements, _root_.List.flatMap_cons, _root_.List.append_assoc] at ih ⊢
    rw [ih]

private theorem assemble_loop_eq {T : Type}
    (iter : core.iter.adapters.rev.Rev (alloc.vec.into_iter.IntoIter (tree.Tree T)))
    (suffix : ProgressiveTree T) {output : ProgressiveTree T}
    (hloop : ProgressiveTree.from_spine_subtrees_loop iter suffix = ok output) :
    output = ProgressiveTree.ofSubtrees iter.iter.val suffix := by
  let inv := fun (state : core.iter.adapters.rev.Rev
      (alloc.vec.into_iter.IntoIter (tree.Tree T)) × ProgressiveTree T) =>
    ProgressiveTree.ofSubtrees state.1.iter.val state.2 = ProgressiveTree.ofSubtrees iter.iter.val suffix
  apply loop_success_invariant
    (fun (state : core.iter.adapters.rev.Rev
      (alloc.vec.into_iter.IntoIter (tree.Tree T)) × ProgressiveTree T) =>
      ProgressiveTree.from_spine_subtrees_loop.body state.1 state.2)
    inv (fun result => result = ProgressiveTree.ofSubtrees iter.iter.val suffix)
    ?_ (iter, suffix) rfl output hloop
  intro ⟨remaining, current⟩ hinv flow hstep
  cases hpop : alloc.vec.Vec.pop Global remaining.iter with
  | fail e =>
    simp [ProgressiveTree.from_spine_subtrees_loop.body,
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      hpop, Bind.bind, Std.bind] at hstep
  | div =>
    simp [ProgressiveTree.from_spine_subtrees_loop.body,
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
      hpop, Bind.bind, Std.bind] at hstep
  | ok result =>
    obtain ⟨entry, rest⟩ := result
    cases entry with
    | none =>
      simp! [ProgressiveTree.from_spine_subtrees_loop.body,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
          alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        hpop, Bind.bind, Std.bind] at hstep
      subst flow
      have hempty := (builder.vec_pop_none_values hpop).1
      simpa [inv, hempty, ProgressiveTree.ofSubtrees] using hinv
    | some entry =>
      simp! [ProgressiveTree.from_spine_subtrees_loop.body,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
          alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        hpop, Bind.bind, Std.bind, alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new,
        triomphe.arc.Arc.new] at hstep
      subst flow
      have hremaining := builder.vec_pop_some_values hpop
      simpa [inv, hremaining, ProgressiveTree.ofSubtrees, _root_.List.foldr_append] using hinv

/-- Successful spine assembly preserves the exact subtree order and produces
    precisely the expected nodes, without any shape or density premise. -/
theorem ProgressiveTree.from_spine_subtrees_eq {T : Type} (ValueInst : Value T)
    (subtrees : alloc.vec.Vec (tree.Tree T)) {output : ProgressiveTree T}
    (hassemble : ProgressiveTree.from_spine_subtrees ValueInst subtrees = ok output) :
    output = ProgressiveTree.ofSubtrees subtrees.val .ProgressiveZero := by
  simp only [ProgressiveTree.from_spine_subtrees, alloc.vec.IntoIteratorVec.into_iter,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_tc_ok] at hassemble
  exact assemble_loop_eq _ _ hassemble

/-- Spine assembly concatenates the materialized sequences of the supplied
    binary subtrees in their original order. -/
theorem ProgressiveTree.from_spine_subtrees_elements {T : Type} (ValueInst : Value T)
    (subtrees : alloc.vec.Vec (tree.Tree T)) {output : ProgressiveTree T}
    (hassemble : ProgressiveTree.from_spine_subtrees ValueInst subtrees = ok output) :
    output.elements = subtrees.val.flatMap tree.Tree.elements := by
  rw [ProgressiveTree.from_spine_subtrees_eq ValueInst subtrees hassemble,
    ProgressiveTree.ofSubtrees_elements]
  simp [ProgressiveTree.elements]

end milhouse.progressive_tree
