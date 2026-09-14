import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- Builder parameters which remain fixed while values are pushed. -/
def Builder.configuration {T : Type} (self : Builder T) :
    Std.Usize × Std.Usize × Option Std.Usize × Std.Usize × Std.Usize :=
  (self.depth, self.level, self.packing_factor, self.packing_depth, self.capacity)

theorem Builder.new_parameters {T : Type} (ValueInst : Value T) (depth level : Std.Usize)
    {self : Builder T}
    (hnew : Builder.new ValueInst depth level = ok (core.result.Result.Ok self)) :
    self.depth = depth ∧ self.level = level ∧ self.length = 0#usize := by
  unfold Builder.new at hnew
  simp only [bind_eq_ok_iff, lift, bind_tc_ok] at hnew
  obtain ⟨packing, _, maximum, _, hnew⟩ := hnew
  split at hnew
  · simp at hnew
  · simp only [bind_eq_ok_iff] at hnew
    obtain ⟨sum, _, capacity, _, factor, _, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    exact ⟨rfl, rfl, rfl⟩

/-- Every successful push preserves depth, level, packing, and capacity.
    No layout or tree invariant is needed for this preservation fact. -/
theorem Builder.push_configuration {T : Type} (ValueInst : Value T)
    (self : Builder T) (value : T) {result : Builder T}
    (hpush : Builder.push ValueInst self value = ok (core.result.Result.Ok (), result)) :
    result.configuration = self.configuration := by
  unfold Builder.push at hpush
  simp only [utils.Length.as_usize, bind_tc_ok] at hpush
  split at hpush
  · simp at hpush
  · rw [bind_eq_ok_iff] at hpush
    obtain ⟨nextIndex, _, hpush⟩ := hpush
    cases hfactor : self.packing_factor with
    | none =>
      rw [hfactor, bind_eq_ok_iff] at hpush
      obtain ⟨top, _, hpush⟩ := hpush
      rw [bind_eq_ok_iff] at hpush
      obtain ⟨zeros, _, hpush⟩ := hpush
      simp only [lift, bind_tc_ok, bind_eq_ok_iff] at hpush
      obtain ⟨⟨status, forest, length⟩, _, hpush⟩ := hpush
      simp! only [ok.injEq, Prod.mk.injEq] at hpush
      obtain ⟨rfl, hresult⟩ := hpush
      subst result
      simp [Builder.configuration, hfactor]
    | some factor =>
      rw [hfactor, bind_eq_ok_iff] at hpush
      obtain ⟨multiple, _, hpush⟩ := hpush
      cases multiple with
      | true =>
        simp only [↓reduceIte] at hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨leaf, _, hpush⟩ := hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨zeros, _, hpush⟩ := hpush
        simp only [lift, bind_tc_ok, bind_eq_ok_iff] at hpush
        obtain ⟨⟨status, forest, length⟩, _, hpush⟩ := hpush
        simp! only [ok.injEq, Prod.mk.injEq] at hpush
        obtain ⟨rfl, hresult⟩ := hpush
        subst result
        simp [Builder.configuration, hfactor]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨⟨entry, forest⟩, _, hpush⟩ := hpush
        dsimp! only at hpush
        cases entry with
        | none => simp at hpush
        | some entry =>
          cases entry with
          | Arced _ => simp at hpush
          | Unarced top =>
            cases top with
            | Leaf _ => simp at hpush
            | Zero _ => simp at hpush
            | Node _ _ _ => simp at hpush
            | PackedLeaf leaf =>
              rw [bind_eq_ok_iff] at hpush
              obtain ⟨⟨status, leaf1⟩, _, hpush⟩ := hpush
              dsimp! only at hpush
              cases status with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                  at hpush
              | Ok success =>
                cases success
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpush
                rw [bind_eq_ok_iff] at hpush
                obtain ⟨zeros, _, hpush⟩ := hpush
                simp only [lift, bind_tc_ok, bind_eq_ok_iff] at hpush
                obtain ⟨⟨status, forest1, length⟩, _, hpush⟩ := hpush
                simp! only [ok.injEq, Prod.mk.injEq] at hpush
                obtain ⟨rfl, hresult⟩ := hpush
                subst result
                simp [Builder.configuration, hfactor]

end milhouse.builder
