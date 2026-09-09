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

/-- Successful application either took the empty-map no-op path, or the
    nonempty path installed the updated tree and computed length with a fresh
    default update map. Both alternatives retain the actual branch answer. This
    is a state characterization, not a claim that bulk updates preserve values. -/
theorem ProgressiveList.apply_updates_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    (mapInst.is_empty self.updates = ok true ∧ result = self) ∨
    ∃ defaults length tree,
      mapInst.is_empty self.updates = ok false ∧
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
      exact Or.inr ⟨defaults, length, tree, hempty, hdefault, hlength, hupdated, happly.symm⟩
    | Err e => simp at happly

/-- A successful nonempty application records the represented merged length
as its backing length. This state fact needs no clone, range, or default-map
laws and includes the actual checked length calculation. -/
theorem ProgressiveList.backing_length_after_nonempty_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) : result.length.val = contents.length := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, _, hlength, _, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · obtain ⟨observed, hobserved, hcontents⟩ := hrep.1
    rw [ProgressiveList.len_eq_updated_length, hlength] at hobserved
    cases hobserved
    exact hcontents

/-- A successful application leaves an empty map. Default construction must
    produce an empty map only on the nonempty branch that uses it; no laws
    about tree updates are needed. -/
theorem ProgressiveList.updates_empty_after_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.is_empty defaults = ok true)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    mapInst.is_empty result.updates = ok true := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨hempty, rfl⟩ | ⟨defaults, length, tree, hempty, hd, _, _, rfl⟩
  · exact hempty
  · exact hdefault hempty defaults hd

/-- The public pending-update observer reports false after successful
    application of updates. -/
theorem ProgressiveList.no_pending_updates_after_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
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
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.is_empty defaults = ok true)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveList.apply_updates ValueInst mapInst result =
      ok (core.result.Result.Ok (), result) := by
  exact ProgressiveList.apply_updates_empty ValueInst mapInst result
    (ProgressiveList.updates_empty_after_apply_updates ValueInst mapInst self hdefault happly)

/-- After successful application, equality of the complete logical-length
results is equivalent to the installed map preserving the new backing extent
on the actual nonempty branch. No representation, packing, clone, range, or
successful metadata premise is needed; the empty branch preserves even an
unsuccessful length result by leaving the original list unchanged. -/
theorem ProgressiveList.len_after_apply_updates_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    ProgressiveList.len ValueInst mapInst result = ProgressiveList.len ValueInst mapInst self ↔
      (mapInst.is_empty self.updates = ok false →
        ∃ largest, mapInst.max_index result.updates = ok largest ∧
          largest.elim result.length.val
            (fun index => max (index.val + 1) result.length.val) = result.length.val) := by
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, rfl⟩ | ⟨defaults, length, newTree, hempty, _, hlength, _, rfl⟩
  · constructor
    · intro _ hfalse
      rw [htrue] at hfalse
      cases hfalse
    · intro _
      rfl
  · have hbefore : ProgressiveList.len ValueInst mapInst self = ok length := by
      rw [ProgressiveList.len_eq_updated_length]
      exact hlength
    constructor
    · intro hlen _
      have hafter := hlen.trans hbefore
      rw [ProgressiveList.len_eq_updated_length] at hafter
      exact (utils.updated_length_eq_ok_iff mapInst length defaults length).mp hafter
    · intro hmax
      have hafter : ProgressiveList.len ValueInst mapInst
          { tree := newTree, length, updates := defaults } = ok length := by
        rw [ProgressiveList.len_eq_updated_length]
        exact (utils.updated_length_eq_ok_iff mapInst length defaults length).mpr (hmax hempty)
      exact hafter.trans hbefore.symm

/-- Successful application preserves the logical length. On the nonempty
    branch, the default map needs only to report no maximum index; no
    precondition on the old length or tree contents is needed. -/
theorem ProgressiveList.len_after_apply_updates {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) {result : ProgressiveList T U}
    (hdefault : mapInst.is_empty self.updates = ok false →
      ∀ defaults, mapInst.coredefaultDefaultInst.default = ok defaults →
      mapInst.max_index defaults = ok none)
    (happly : ProgressiveList.apply_updates ValueInst mapInst self =
      ok (core.result.Result.Ok (), result)) :
    ProgressiveList.len ValueInst mapInst result =
      ProgressiveList.len ValueInst mapInst self := by
  apply (ProgressiveList.len_after_apply_updates_iff ValueInst mapInst self happly).mpr
  intro hempty
  rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
    ⟨htrue, _⟩ | ⟨defaults, length, tree, _, hd, _, _, rfl⟩
  · rw [hempty] at htrue
    cases htrue
  · exact ⟨none, hdefault hempty defaults hd, rfl⟩

end milhouse.progressive_list
