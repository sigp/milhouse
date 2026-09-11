import Tree.Cow.Metadata

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- Attach a new maximum borrow, retaining an existing callback chain. The
empty inline slot reuses its tail; a present slot is linked below the new one. -/
def CowOnMut.attachIndex (self : CowOnMut) (state : update_map.MaxIndexState)
    (index : Std.Usize) : CowOnMut :=
  .mk (some (state, index))
    (match self.max_index with | none => self.previous | some _ => some self)

/-- Return the inner callback chain and the new wrapper's maximum borrow.
Incompatible callback shapes restore the original borrowed state. -/
def CowOnMut.releaseIndex (self : CowOnMut) (state : update_map.MaxIndexState)
    (replacement : CowOnMut) : CowOnMut × update_map.MaxIndexState :=
  match self.max_index, replacement with
  | some _, .mk (some (next, _)) (some previous) => (previous, next)
  | none, .mk (some (next, _)) previous => (.mk none previous, next)
  | _, _ => (self, state)

/-- The exact source attachment and backward continuation, with no bound
on callback-chain depth or condition on the original metadata. -/
theorem CowOnMut.with_max_index_eq (self : CowOnMut)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    CowOnMut.with_max_index self state index =
      ok (self.attachIndex state index, self.releaseIndex state) := by
  cases self with
  | mk action previous =>
    cases action <;> apply congrArg ok <;> apply Prod.ext
    all_goals
      first
      | rfl
      | funext replacement
        cases replacement with
        | mk action previous =>
          cases action with
          | none => rfl
          | some pair =>
            cases previous with
            | none => rfl
            | some previous => cases previous; rfl

theorem CowOnMut.attachIndex_max_index (self : CowOnMut)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    (self.attachIndex state index).max_index = some (state, index) := rfl

/-- Releasing an unchanged attachment restores both borrows, at any depth. -/
theorem CowOnMut.releaseIndex_attachIndex (self : CowOnMut)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    self.releaseIndex state (self.attachIndex state index) = (self, state) := by
  cases self with
  | mk action previous => cases action <;> rfl

/-- Materializing an attached chain records both the original callbacks
and the newly attached maximum. No callback-neutrality premise is needed. -/
theorem CowOnMut.releaseIndex_recorded_attachIndex (self : CowOnMut)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    self.releaseIndex state (self.attachIndex state index).recorded =
      (self.recorded, state.recorded index) := by
  cases self with
  | mk action previous => cases action <;> cases previous <;> rfl

end milhouse.cow
