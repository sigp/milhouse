import Tree.ProgressiveList.Clone

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- The backing tree is installed only after successful rebasing. An error
    returns the original list, including its original pending updates. -/
theorem ProgressiveList.rebase_on_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) :
    ProgressiveList.rebase_on ValueInst mapInst self base = (do
      let rebased ← progressive_tree.ProgressiveTree.rebase_on ValueInst self.tree base.tree self.length base.length
      match rebased with
      | core.result.Result.Ok tree => ok (core.result.Result.Ok (), { self with tree })
      | core.result.Result.Err error => ok (core.result.Result.Err error, self)) := by
  unfold ProgressiveList.rebase_on
  simp only [utils.Length.as_usize, bind_tc_ok]
  cases progressive_tree.ProgressiveTree.rebase_on ValueInst self.tree base.tree self.length base.length with
  | fail e => rfl
  | div => rfl
  | ok rebased =>
    cases rebased <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]

theorem ProgressiveList.rebase_on_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (core.result.Result.Ok (), result)) :
    ∃ tree, progressive_tree.ProgressiveTree.rebase_on ValueInst self.tree base.tree self.length base.length =
      ok (core.result.Result.Ok tree) ∧ result = { self with tree } := by
  rw [ProgressiveList.rebase_on_eq, bind_eq_ok_iff] at hrebase
  obtain ⟨rebased, hrebased, hrebase⟩ := hrebase
  cases rebased with
  | Err e => simp at hrebase
  | Ok tree =>
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hrebase
    exact ⟨tree, hrebased, hrebase.symm⟩

theorem ProgressiveList.rebase_on_error_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) {result : ProgressiveList T U} {error : error.Error}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (core.result.Result.Err error, result)) :
    result = self := by
  rw [ProgressiveList.rebase_on_eq, bind_eq_ok_iff] at hrebase
  obtain ⟨rebased, _, hrebase⟩ := hrebase
  cases rebased with
  | Err e =>
    simp only [ok.injEq, Prod.mk.injEq] at hrebase
    exact hrebase.2.symm
  | Ok tree => simp at hrebase

/-- Both success and returned errors preserve the backing length and exact
    pending-map state. Neither input needs a representation invariant. -/
theorem ProgressiveList.rebase_on_preserves_metadata {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) {result : ProgressiveList T U}
    {status : core.result.Result Unit error.Error}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (status, result)) :
    result.length = self.length ∧ result.updates = self.updates := by
  cases status with
  | Err e =>
    rw [ProgressiveList.rebase_on_error_preserves_self ValueInst mapInst self base hrebase]
    exact ⟨rfl, rfl⟩
  | Ok value =>
    cases value
    obtain ⟨tree, _, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
    exact ⟨rfl, rfl⟩

/-- Logical length and the public pending-update observer are unchanged on
    every returned result, without assumptions about map behavior. -/
theorem ProgressiveList.rebase_on_preserves_observers {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) {result : ProgressiveList T U}
    {status : core.result.Result Unit error.Error}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (status, result)) :
    ProgressiveList.len ValueInst mapInst result = ProgressiveList.len ValueInst mapInst self ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result =
        ProgressiveList.has_pending_updates ValueInst mapInst self := by
  obtain ⟨hlength, hupdates⟩ := ProgressiveList.rebase_on_preserves_metadata ValueInst mapInst self base hrebase
  simp only [ProgressiveList.len, hlength, hupdates, ProgressiveList.has_pending_updates, and_self]

/-- Successful nonmutating rebasing clones first and then completes the same
    in-place operation. This exposes actual calls for the content proof. -/
theorem ProgressiveList.rebase_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (core.result.Result.Ok result)) :
    ∃ cloned, ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok cloned ∧
      ProgressiveList.rebase_on ValueInst mapInst cloned base = ok (core.result.Result.Ok (), result) := by
  unfold ProgressiveList.rebase at hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨cloned, hcloned, hrebase⟩ := hrebase
  rw [bind_eq_ok_iff] at hrebase
  obtain ⟨⟨status, after⟩, hafter, hrebase⟩ := hrebase
  dsimp! only at hrebase
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at hrebase
  | Ok value =>
    cases value
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hrebase
    subst after
    exact ⟨cloned, hcloned, hafter⟩

/-- Every successful nonmutating rebase keeps the recorded backing length
and returns precisely the pending-map clone performed at entry. This fact is
independent of structural invariants and of any clone-preservation law. -/
theorem ProgressiveList.rebase_preserves_metadata {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, hupdates, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  obtain ⟨hlength, hmap⟩ := ProgressiveList.rebase_on_preserves_metadata ValueInst mapInst
    { self with updates } base hrebased
  exact ⟨hlength, by simpa only [hmap] using hupdates⟩

/-- Nonmutating rebasing preserves length and pending-update observers when
the actual map clone preserves maximum and emptiness. No element, cache,
representation, or read-preservation law is needed for these observers. -/
theorem ProgressiveList.rebase_preserves_observers {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      mapInst.max_index updates = mapInst.max_index self.updates)
    (hmapEmpty : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      mapInst.is_empty updates = mapInst.is_empty self.updates)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    ProgressiveList.len ValueInst mapInst result = ProgressiveList.len ValueInst mapInst self ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result =
        ProgressiveList.has_pending_updates ValueInst mapInst self := by
  obtain ⟨hlength, hclone⟩ := ProgressiveList.rebase_preserves_metadata ValueInst mapInst self base hrebase
  simp only [ProgressiveList.len, hlength, utils.updated_length, hmapMax result.updates hclone,
    ProgressiveList.has_pending_updates, hmapEmpty result.updates hclone, and_self]

end milhouse.progressive_list
