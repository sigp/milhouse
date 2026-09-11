import Tree.Cow.Value

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- The metadata state after recording one inserted key. -/
def MaxIndexState.recorded (self : MaxIndexState) (index : Std.Usize) : MaxIndexState :=
  match self with
  | .Empty => .Known index
  | .Known previous => .Known (core.cmp.impls.OrdUsize.max previous index)

/-- Recording an insertion succeeds and stores the maximum of the old key
    and the inserted key, including an initially empty metadata state. -/
theorem MaxIndexState.record_insert_eq (self : MaxIndexState) (index : Std.Usize) :
    MaxIndexState.record_insert self index = ok (self.recorded index) := by
  cases self with
  | Empty => rfl
  | Known previous =>
    simp only [MaxIndexState.record_insert, MaxIndexState.recorded]
    by_cases hgreater : index > previous
    · rw [if_pos hgreater]
      congr 2
      apply UScalar.eq_of_val_eq
      rw [core.cmp.impls.OrdUsize.max_val, max_eq_right (by scalar_tac)]
    · rw [if_neg hgreater]
      congr 2
      apply UScalar.eq_of_val_eq
      rw [core.cmp.impls.OrdUsize.max_val, max_eq_left (by scalar_tac)]

end milhouse.update_map

namespace milhouse.cow

/-- Metadata returned to every original borrow after materialization. -/
def CowOnMut.recorded : CowOnMut → CowOnMut
  | .mk action none =>
      .mk (action.map (fun (state, index) => (state.recorded index, index))) none
  | .mk action (some previous) =>
      .mk (action.map (fun (state, index) => (state.recorded index, index)))
        (some previous.recorded)

@[simp] theorem CowOnMut.eta (self : CowOnMut) :
    CowOnMut.mk self.max_index self.previous = self := by
  cases self; rfl

/-- Running the callback chain clears every action. Its backward continuation
records all original maximum borrows, independently of subsequent state. -/
theorem CowOnMut.run_eq (self : CowOnMut) :
    CowOnMut.run self = ok (.mk none none, fun _ => self.recorded) := by
  cases self with
  | mk action previous =>
    cases previous with
    | none =>
      rw [CowOnMut.run]
      cases action with
      | none => rfl
      | some pair =>
        obtain ⟨state, index⟩ := pair
        simp [CowOnMut.max_index, CowOnMut.previous, CowOnMut.recorded,
          update_map.MaxIndexState.record_insert_eq]
    | some previous =>
      rw [CowOnMut.run]
      simp! only [CowOnMut.previous._simpLemma_, CowOnMut.max_index._simpLemma_,
        CowOnMut.run_eq previous, bind_tc_ok, CowOnMut.eta]
      cases action with
      | none => simp
      | some pair =>
        obtain ⟨state, index⟩ := pair
        simp [update_map.MaxIndexState.record_insert_eq]
termination_by sizeOf self

/-- Running the cleared chain again has no effect. Both continuations together
return exactly the metadata recorded by the first run, at every chain depth. -/
theorem CowOnMut.run_twice (self : CowOnMut) :
    ∃ cleared firstBack secondBack,
      CowOnMut.run self = ok (cleared, firstBack) ∧
      CowOnMut.run cleared = ok (cleared, secondBack) ∧
      ∀ later, firstBack (secondBack later) = firstBack cleared := by
  rw [CowOnMut.run_eq]
  exact ⟨.mk none none, fun _ => self.recorded,
    fun _ => .mk none none, rfl, CowOnMut.run_eq _, fun _ => rfl⟩

end milhouse.cow
