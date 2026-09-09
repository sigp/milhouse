import Tree.ProgressiveList.PopFront.State
import Tree.ProgressiveTree.Builder.Caches

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Streaming reconstruction preserves cleared builder caches, independently
of iterator finiteness, yielded values, or clone behavior. -/
theorem ProgressiveListIter.extend_builder_preserves_cleared_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    (hcache : initial.CachesCleared)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result)) :
    result.CachesCleared := by
  let inv := fun (state : ProgressiveListIter T U × ProgressiveTreeBuilder T) =>
    state.2.CachesCleared
  let post := fun (result : core.result.Result Unit error.Error × ProgressiveTreeBuilder T) =>
    result.1 = core.result.Result.Ok () → result.2.CachesCleared
  have hbody : ∀ state, inv state → ∀ flow,
      ProgressiveListIter.extend_builder_loop.body ValueInst mapInst state.1 state.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, current⟩ hinv flow hstep
    unfold ProgressiveListIter.extend_builder_loop.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, cursor1⟩, _, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none =>
      simp only [ok.injEq] at hstep
      subst flow
      exact fun _ => hinv
    | some entry =>
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨value, _, hstep⟩ := hstep
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨⟨status, pushed⟩, hpush, hstep⟩ := hstep
      dsimp! only at hstep
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hstep
        subst flow
        simp [post]
      | Ok success =>
        cases success
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, ok.injEq] at hstep
        subst flow
        exact ProgressiveTreeBuilder.push_preserves_cleared_caches ValueInst current value hinv hpush
  exact loop_success_invariant
    (fun state => ProgressiveListIter.extend_builder_loop.body ValueInst mapInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (self, initial) hcache _ hextend rfl


/-- Every successful nonzero front removal constructs entirely cleared caches.
It needs no invariant on the old caches, nor any clone, map, or shape laws. -/
theorem ProgressiveList.pop_front_nonzero_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (n : Std.Usize) (hnonzero : n ≠ 0#usize)
    {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (.Ok (), result)) :
    result.tree.CachesCleared := by
  rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
    ⟨hzero, _⟩ | ⟨_, beforeLength, cursor, initial, built, output, length, updates,
      _, _, _, hnew, hextend, hfinish, _, rfl⟩
  · exact False.elim (hnonzero hzero)
  · have hinitial := ProgressiveTreeBuilder.new_caches_cleared ValueInst hnew
    have hbuilt := ProgressiveListIter.extend_builder_preserves_cleared_caches
      ValueInst mapInst cursor initial hinitial hextend
    exact ProgressiveTreeBuilder.finish_caches_cleared ValueInst built hbuilt hfinish

/-- Every returned front-removal state preserves any cache predicate accepting
zero: errors restore the original list, zero removal is a no-op, and nonzero
success builds cleared caches internally. -/
theorem ProgressiveList.pop_front_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8))
    (self : ProgressiveList T U) (n : Std.Usize) (hcache : self.tree.CachesOn P 0)
    {status : core.result.Result Unit error.Error} {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (status, result)) :
    result.tree.CachesOn P 0 := by
  cases status with
  | Err error =>
    rw [ProgressiveList.pop_front_error_preserves ValueInst mapInst self n hpop]
    exact hcache
  | Ok success =>
    cases success
    by_cases hn : n = 0#usize
    · subst n
      rw [ProgressiveList.pop_front_zero] at hpop
      have hresult : self = result := (Prod.mk.inj (Result.ok.inj hpop)).2
      subst result
      exact hcache
    · exact (ProgressiveList.pop_front_nonzero_caches_cleared
        ValueInst mapInst self n hn hpop).cachesOn P hzero 0

theorem ProgressiveList.pop_front_preserves_valid_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash)
    (self : ProgressiveList T U) (n : Std.Usize)
    (hcache : self.tree.CachesOn (CacheValidFor reference) 0)
    {status : core.result.Result Unit error.Error} {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (status, result)) :
    result.tree.CachesOn (CacheValidFor reference) 0 :=
  ProgressiveList.pop_front_preserves_caches ValueInst mapInst
    (CacheValidFor reference) (CacheValidFor.zero reference) self n hcache hpop

end milhouse.progressive_list
