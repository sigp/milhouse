import Tree.ProgressiveList.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Applying an empty update map is a successful no-op. It does not need
    default construction, tree validity, or map metadata beyond this answer. -/
theorem ProgressiveList.apply_updates_empty {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    (hempty : mapInst.is_empty self.updates = ok true) :
    ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), self) := by
  simp [ProgressiveList.apply_updates, hempty]

/-- When applying updates returns a Rust error, the entire list state is
    restored, including pending updates. This needs no correctness assumptions
    about the map or the tree; it follows from the operation's error path. -/
theorem ProgressiveList.apply_updates_error_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U} {error : error.Error}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Err error, result)) : result = self := by
  unfold ProgressiveList.apply_updates at happly
  rw [bind_eq_ok_iff] at happly
  obtain ⟨empty, hempty, happly⟩ := happly
  cases empty with
  | true => simp at happly
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at happly
    rw [bind_eq_ok_iff] at happly
    obtain ⟨taken, htake, happly⟩ := happly
    unfold core.mem.take at htake
    rw [bind_eq_ok_iff] at htake
    obtain ⟨default, hdefault, htake⟩ := htake
    simp only [ok.injEq] at htake
    subst taken
    change (utils.updated_length mapInst self.length self.updates >>= _) = _ at happly
    rw [bind_eq_ok_iff] at happly
    obtain ⟨length, hlength, happly⟩ := happly
    simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at happly
    rw [bind_eq_ok_iff] at happly
    obtain ⟨updated, hupdated, happly⟩ := happly
    cases updated with
    | Ok tree => simp [triomphe.arc.Arc.new] at happly
    | Err e =>
      simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at happly
      exact happly.2.symm

/-- Successful application either took the empty-map no-op path, or installed
    the updated tree and computed length with a fresh default update map. This
    is a state characterization, not a claim that bulk updates preserve values. -/
theorem ProgressiveList.apply_updates_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    (mapInst.is_empty self.updates = ok true ∧ result = self) ∨
    ∃ defaults length tree,
      mapInst.coredefaultDefaultInst.default = ok defaults ∧
      utils.updated_length mapInst self.length self.updates = ok length ∧
      progressive_tree.ProgressiveTree.with_updated_leaves ValueInst mapInst
        self.tree self.updates = ok (core.result.Result.Ok tree) ∧
      result = { tree, length, updates := defaults } := by
  unfold ProgressiveList.apply_updates at happly
  rw [bind_eq_ok_iff] at happly
  obtain ⟨empty, hempty, happly⟩ := happly
  cases empty with
  | true =>
    simp at happly
    exact Or.inl ⟨hempty, happly.symm⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at happly
    rw [bind_eq_ok_iff] at happly
    obtain ⟨taken, htake, happly⟩ := happly
    unfold core.mem.take at htake
    rw [bind_eq_ok_iff] at htake
    obtain ⟨defaults, hdefault, htake⟩ := htake
    simp only [ok.injEq] at htake
    subst taken
    change (utils.updated_length mapInst self.length self.updates >>= _) = _ at happly
    rw [bind_eq_ok_iff] at happly
    obtain ⟨length, hlength, happly⟩ := happly
    simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at happly
    rw [bind_eq_ok_iff] at happly
    obtain ⟨updated, hupdated, happly⟩ := happly
    cases updated with
    | Ok tree =>
      simp [triomphe.arc.Arc.new] at happly
      exact Or.inr ⟨defaults, length, tree, hdefault, hlength, hupdated, happly.symm⟩
    | Err e => simp at happly

/-- A successful application leaves an empty map, provided default construction
    produces an empty map. No laws about tree updates are needed. -/
theorem ProgressiveList.updates_empty_after_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.is_empty defaults = ok true)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    mapInst.is_empty result.updates = ok true := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨hempty, rfl⟩ | ⟨defaults, length, tree, hd, _, _, rfl⟩
  · exact hempty
  · exact hdefault defaults hd

/-- The public pending-update observer reports false after successful
    application of updates. -/
theorem ProgressiveList.no_pending_updates_after_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.is_empty defaults = ok true)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  exact ProgressiveList.has_pending_updates_spec ValueInst mapInst result true
    (ProgressiveList.updates_empty_after_apply_updates ValueInst mapInst self hdefault happly)

/-- Once updates have been applied successfully, applying them again succeeds
    and leaves the entire list unchanged. -/
theorem ProgressiveList.apply_updates_idempotent {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.is_empty defaults = ok true)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveList.apply_updates ValueInst mapInst result =
      ok (core.result.Result.Ok (), result) := by
  exact ProgressiveList.apply_updates_empty ValueInst mapInst result
    (ProgressiveList.updates_empty_after_apply_updates ValueInst mapInst self hdefault happly)

/-- Successful application preserves the logical length. The default map needs
    only to report no maximum index; no precondition on the old length, old map
    metadata, or tree contents is needed. -/
theorem ProgressiveList.len_after_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.max_index defaults = ok none)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveList.len ValueInst mapInst result =
      ProgressiveList.len ValueInst mapInst self := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨_, rfl⟩ | ⟨defaults, length, tree, hd, hlength, _, rfl⟩
  · rfl
  · rw [ProgressiveList.len_of_no_max_index ValueInst mapInst _ (hdefault defaults hd),
      ProgressiveList.len_eq_updated_length, hlength]

end milhouse.progressive_list
