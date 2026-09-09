import Tree.ProgressiveTree.Builder.Spine

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Spine assembly terminates after consuming the supplied subtrees from the
back and returns their exact ordered fold around the existing suffix. -/
theorem ProgressiveTree.from_spine_subtrees_loop_success {T : Type}
    (iter : core.iter.adapters.rev.Rev (alloc.vec.into_iter.IntoIter (tree.Tree T)))
    (suffix : ProgressiveTree T) :
    ProgressiveTree.from_spine_subtrees_loop iter suffix =
      ok (ProgressiveTree.ofSubtrees iter.iter.val suffix) := by
  by_cases hempty : iter.iter.val = []
  · have hpop : alloc.vec.Vec.pop Global iter.iter = ok (none, iter.iter) := by
      have heq : iter.iter = (⟨[], by simp⟩ : alloc.vec.Vec (tree.Tree T)) := Subtype.ext hempty
      rw [heq]
      rfl
    have hbody : ProgressiveTree.from_spine_subtrees_loop.body iter suffix = ok (.done suffix) := by
      simp! only [ProgressiveTree.from_spine_subtrees_loop.body,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        hpop, Bind.bind, Std.bind]
    rw [ProgressiveTree.from_spine_subtrees_loop, loop]
    simp! only [hbody, bind_tc_ok, hempty, ProgressiveTree.ofSubtrees, _root_.List.foldr_nil]
  · let items := iter.iter.val.dropLast
    let entry := iter.iter.val.getLast hempty
    have hentries : iter.iter.val = items ++ [entry] :=
      (_root_.List.dropLast_concat_getLast hempty).symm
    obtain ⟨rest, hpop, hrest⟩ := vec_pop_append_last (A := Global) iter.iter items entry hentries
    let nextIter : core.iter.adapters.rev.Rev (alloc.vec.into_iter.IntoIter (tree.Tree T)) := { iter := rest }
    let nextSuffix := ProgressiveTree.ProgressiveNode (Array.repeat 32#usize 0#u8) entry suffix
    have hbody : ProgressiveTree.from_spine_subtrees_loop.body iter suffix =
        ok (.cont (nextIter, nextSuffix)) := by
      simp! only [ProgressiveTree.from_spine_subtrees_loop.body,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        hpop, Bind.bind, Std.bind, alloy_primitives.bits.fixed.FixedBytes.ZERO,
        lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new, nextIter, nextSuffix]
    have hloop := ProgressiveTree.from_spine_subtrees_loop_success nextIter nextSuffix
    rw [ProgressiveTree.from_spine_subtrees_loop, loop]
    simp! only [hbody, bind_tc_ok]
    change ProgressiveTree.from_spine_subtrees_loop nextIter nextSuffix = _
    rw [hloop]
    congr 1
    simp only [ProgressiveTree.ofSubtrees, nextIter, hrest, hentries,
      _root_.List.foldr_append, _root_.List.foldr_cons, _root_.List.foldr_nil, nextSuffix]
termination_by iter.iter.val.length
decreasing_by
  have hlength := congrArg _root_.List.length hentries
  simp only [_root_.List.length_append, _root_.List.length_singleton] at hlength
  change rest.val.length < iter.iter.val.length
  rw [hrest]
  omega

/-- Building a progressive spine always succeeds and preserves exact subtree
order. Shape, packing, and capacity conditions are unnecessary for assembly. -/
theorem ProgressiveTree.from_spine_subtrees_success {T : Type} (ValueInst : Value T)
    (subtrees : alloc.vec.Vec (tree.Tree T)) :
    ProgressiveTree.from_spine_subtrees ValueInst subtrees =
      ok (ProgressiveTree.ofSubtrees subtrees.val .ProgressiveZero) := by
  simp only [ProgressiveTree.from_spine_subtrees, alloc.vec.IntoIteratorVec.into_iter,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_tc_ok]
  exact ProgressiveTree.from_spine_subtrees_loop_success _ _

end milhouse.progressive_tree
