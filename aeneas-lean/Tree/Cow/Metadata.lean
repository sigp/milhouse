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

/-- Running the callback clears it immediately. Its backward continuation
    returns the recorded maximum to the original borrow, independently of
    subsequent callback state. -/
theorem CowOnMut.run_eq (self : CowOnMut) :
    CowOnMut.run self = ok
      ({ max_index := none }, fun _ =>
        { max_index := self.max_index.map (fun (state, index) => (state.recorded index, index)) }) := by
  obtain ⟨action⟩ := self
  cases action with
  | none => rfl
  | some action =>
    obtain ⟨state, index⟩ := action
    simp [CowOnMut.run, update_map.MaxIndexState.record_insert_eq]

/-- After one run, another run has no action to execute. Composing the two
    backward continuations returns exactly the first recorded metadata. -/
theorem CowOnMut.run_twice (self : CowOnMut) :
    ∃ cleared firstBack secondBack,
      CowOnMut.run self = ok (cleared, firstBack) ∧
      CowOnMut.run cleared = ok (cleared, secondBack) ∧
      ∀ later, firstBack (secondBack later) = firstBack cleared := by
  rw [CowOnMut.run_eq]
  refine ⟨{ max_index := none },
    fun _ => { max_index := self.max_index.map (fun (state, index) => (state.recorded index, index)) },
    fun _ => { max_index := none }, rfl, rfl, ?_⟩
  intro later
  rfl

/-- Attaching maximum-index tracking changes no carried value. Releasing the
    attached handle unchanged restores the exact original handle and maximum,
    so read-only access does not record an insertion. -/
theorem Cow.with_max_index_roundtrip {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (state : update_map.MaxIndexState) (index : Std.Usize) :
    ∃ attached back,
      Cow.with_max_index cloneInst self state index = ok (attached, back) ∧
      attached.value = self.value ∧ attached.onMut.max_index = some (state, index) ∧
      back attached = (self, state) := by
  cases self with
  | BTree inner action =>
    refine ⟨_, _, rfl, ?_, rfl, rfl⟩
    cases inner <;> rfl
  | Vec inner action =>
    refine ⟨_, _, rfl, ?_, rfl, rfl⟩
    cases inner <;> rfl

end milhouse.cow
