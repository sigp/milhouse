import Tree.Builder.Caches.Push
import Tree.Builder.Caches.Finish
import Tree.ProgressiveTree.Builder.Contents

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- Every completed subtree and the current builder have cleared caches. -/
def ProgressiveTreeBuilder.CachesCleared {T : Type} (self : ProgressiveTreeBuilder T) : Prop :=
  (∀ subtree ∈ self.subtrees.val, subtree.CachesCleared) ∧ self.current.CachesCleared

private theorem subtrees_push_caches {T : Type} {before after : alloc.vec.Vec (tree.Tree T)}
    {last : tree.Tree T} (hbefore : ∀ subtree ∈ before.val, subtree.CachesCleared)
    (hlast : last.CachesCleared) (hpush : alloc.vec.Vec.push before last = ok after) :
    ∀ subtree ∈ after.val, subtree.CachesCleared := by
  rw [vec_push_values hpush]
  intro subtree hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hbefore subtree hmem
  · have heq : subtree = last := by simpa using hmem
    subst subtree
    exact hlast

theorem ProgressiveTree.ofSubtrees_caches_cleared {T : Type}
    (subtrees : _root_.List (tree.Tree T)) (suffix : ProgressiveTree T)
    (hsubtrees : ∀ subtree ∈ subtrees, subtree.CachesCleared) (hsuffix : suffix.CachesCleared) :
    (ProgressiveTree.ofSubtrees subtrees suffix).CachesCleared := by
  induction subtrees with
  | nil => exact hsuffix
  | cons head tail ih =>
    exact ⟨rfl, hsubtrees head (by simp), ih (fun subtree hmem => hsubtrees subtree (by simp [hmem]))⟩

/-- Spine assembly clears each new progressive cache and retains the cleared
caches of its input subtrees, independently of their shapes. -/
theorem ProgressiveTree.from_spine_subtrees_caches_cleared {T : Type} (ValueInst : Value T)
    (subtrees : alloc.vec.Vec (tree.Tree T)) {output : ProgressiveTree T}
    (hsubtrees : ∀ subtree ∈ subtrees.val, subtree.CachesCleared)
    (hassemble : ProgressiveTree.from_spine_subtrees ValueInst subtrees = ok output) :
    output.CachesCleared := by
  rw [ProgressiveTree.from_spine_subtrees_eq ValueInst subtrees hassemble]
  exact ProgressiveTree.ofSubtrees_caches_cleared _ _ hsubtrees (by trivial)

/-- A fresh progressive builder has cleared caches. -/
theorem ProgressiveTreeBuilder.new_caches_cleared {T : Type} (ValueInst : Value T)
    {self : ProgressiveTreeBuilder T}
    (hnew : ProgressiveTreeBuilder.new ValueInst = ok (core.result.Result.Ok self)) :
    self.CachesCleared := by
  unfold ProgressiveTreeBuilder.new at hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨depth, _, hnew⟩ := hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨status, hcurrent, hnew⟩ := hnew
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hnew
  | Ok current =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hnew
    rw [bind_eq_ok_iff] at hnew
    obtain ⟨capacity, _, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    exact ⟨by simp, Builder.new_caches_cleared ValueInst _ _ hcurrent⟩

private theorem pushTail_caches_cleared {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) (value : T) (hself : self.CachesCleared)
    {result : ProgressiveTreeBuilder T}
    (hpush : ProgressiveTreeBuilder.pushTail ValueInst self value = ok (core.result.Result.Ok (), result)) :
    result.CachesCleared := by
  unfold ProgressiveTreeBuilder.pushTail at hpush
  rw [bind_eq_ok_iff] at hpush
  obtain ⟨⟨status, current⟩, hcurrent, hpush⟩ := hpush
  dsimp! only at hpush
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
  | Ok success =>
    cases success
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, bind_eq_ok_iff] at hpush
    obtain ⟨count, _, length, _, hpush⟩ := hpush
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hpush
    subst result
    exact ⟨hself.1, Builder.push_preserves_cleared_caches ValueInst _ _ hself.2 hcurrent⟩

/-- Every successful push preserves cleared caches, including rollover from
a completed binary subtree to a fresh builder. -/
theorem ProgressiveTreeBuilder.push_preserves_cleared_caches {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) (value : T) (hself : self.CachesCleared)
    {result : ProgressiveTreeBuilder T}
    (hpush : ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result)) :
    result.CachesCleared := by
  unfold ProgressiveTreeBuilder.push at hpush
  split at hpush
  · rw [bind_eq_ok_iff] at hpush
    obtain ⟨depth, _, hpush⟩ := hpush
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨binaryDepth, _, hpush⟩ := hpush
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨status, hnew, hpush⟩ := hpush
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
    | Ok current =>
      simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, core.mem.replace] at hpush
      rw [bind_eq_ok_iff] at hpush
      obtain ⟨status, hfinish, hpush⟩ := hpush
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
      | Ok output =>
        obtain ⟨output, outputDepth, outputLength⟩ := output
        simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨subtrees, hsubtrees, hpush⟩ := hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨capacity, _, hpush⟩ := hpush
        let prepared := {self with subtrees, current, prog_depth := depth, capacity, count := 0#usize}
        change ProgressiveTreeBuilder.pushTail ValueInst prepared value = ok (core.result.Result.Ok (), result) at hpush
        have hfinished := Builder.finish_caches_cleared ValueInst _ hself.2 hfinish
        have hprepared : prepared.CachesCleared :=
          ⟨subtrees_push_caches hself.1 hfinished hsubtrees,
            Builder.new_caches_cleared ValueInst _ _ hnew⟩
        exact pushTail_caches_cleared ValueInst prepared value hprepared hpush
  · exact pushTail_caches_cleared ValueInst self value hself hpush

/-- Successful finalization returns a progressive tree with cleared caches.
No counter agreement is needed: skipping the current builder when the count
is zero cannot introduce a nonzero cache. -/
theorem ProgressiveTreeBuilder.finish_caches_cleared {T : Type} (ValueInst : Value T)
    (self : ProgressiveTreeBuilder T) {output : ProgressiveTree T} {length : Std.Usize}
    (hself : self.CachesCleared)
    (hfinish : ProgressiveTreeBuilder.finish ValueInst self =
      ok (core.result.Result.Ok (output, length))) :
    output.CachesCleared := by
  unfold ProgressiveTreeBuilder.finish at hfinish
  split at hfinish
  · rw [bind_eq_ok_iff] at hfinish
    obtain ⟨status, hcurrent, hfinish⟩ := hfinish
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hfinish
    | Ok result =>
      obtain ⟨current, depth, currentLength⟩ := result
      simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨subtrees, hsubtrees, hfinish⟩ := hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨assembled, hassemble, hfinish⟩ := hfinish
      simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
      obtain ⟨rfl, rfl⟩ := hfinish
      exact ProgressiveTree.from_spine_subtrees_caches_cleared ValueInst _
        (subtrees_push_caches hself.1
          (Builder.finish_caches_cleared ValueInst _ hself.2 hcurrent) hsubtrees) hassemble
  · rw [bind_eq_ok_iff] at hfinish
    obtain ⟨assembled, hassemble, hfinish⟩ := hfinish
    simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hfinish
    obtain ⟨rfl, rfl⟩ := hfinish
    exact ProgressiveTree.from_spine_subtrees_caches_cleared ValueInst _ hself.1 hassemble

end milhouse.progressive_tree
