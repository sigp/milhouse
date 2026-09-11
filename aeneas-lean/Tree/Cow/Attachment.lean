import Tree.Cow.Consuming

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- The handle data after attaching the wrapper's maximum-index borrow. -/
def Cow.attachIndex {T : Type} (self : Cow T) (state : update_map.MaxIndexState)
    (index : Std.Usize) : Cow T :=
  match self with
  | .BTree inner _ => .BTree inner ⟨some (state, index)⟩
  | .Vec inner _ => .Vec inner ⟨some (state, index)⟩

/-- The exact attachment continuation. It restores the original inner
callback and returns the wrapper's borrowed metadata separately. Inputs with
an incompatible variant or absent callback restore the original loan. -/
def Cow.releaseIndex {T : Type} (self : Cow T) (state : update_map.MaxIndexState)
    (replacement : Cow T) : Cow T × update_map.MaxIndexState :=
  match self, replacement with
  | .BTree _ action, .BTree inner ⟨some (next, _)⟩ => (.BTree inner action, next)
  | .Vec _ action, .Vec inner ⟨some (next, _)⟩ => (.Vec inner action, next)
  | _, _ => (self, state)

/-- Attachment is total and has exactly the extracted backward continuation,
without cloning, entry, or metadata assumptions. -/
theorem Cow.with_max_index_eq {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (state : update_map.MaxIndexState) (index : Std.Usize) :
    Cow.with_max_index cloneInst self state index =
      ok (self.attachIndex state index, self.releaseIndex state) := by
  cases self with
  | BTree inner action =>
    apply congrArg ok
    apply Prod.ext
    · rfl
    · funext replacement
      cases replacement with
      | BTree replacement callback =>
        cases callback with
        | mk value => cases value <;> rfl
      | Vec _ _ => rfl
  | Vec inner action =>
    apply congrArg ok
    apply Prod.ext
    · rfl
    · funext replacement
      cases replacement with
      | BTree _ _ => rfl
      | Vec replacement callback =>
        cases callback with
        | mk value => cases value <;> rfl

theorem Cow.attachIndex_value {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    (self.attachIndex state index).value = self.value := by
  cases self <;> rename_i inner action <;> cases inner <;> rfl

theorem Cow.attachIndex_entryAt {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index query : Std.Usize) :
    (self.attachIndex state index).EntryAt query ↔ self.EntryAt query := by
  cases self with
  | BTree inner action =>
    cases inner with
    | Mutable _ => rfl
    | Immutable _ entry => cases entry <;> rfl
  | Vec inner action =>
    cases inner with
    | Mutable _ => rfl
    | Immutable _ entry => cases entry <;> rfl

theorem Cow.attachIndex_needsClone {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    (self.attachIndex state index).NeedsClone = self.NeedsClone := by
  cases self <;> rename_i inner action <;> cases inner <;> rfl

/-- Releasing the attached handle unchanged restores both original borrows. -/
theorem Cow.releaseIndex_attachIndex {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    self.releaseIndex state (self.attachIndex state index) = (self, state) := by
  cases self <;> rfl

/-- Every actual filled footprint records the wrapper key. This conclusion
does not depend on the inner callback, map laws, cloning, or index bounds. -/
theorem Cow.releaseIndex_written_maximum {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) (replacement : T)
    {changed : Cow T}
    (hwritten : (self.attachIndex state index).Written replacement changed) :
    (self.releaseIndex state changed).2 = state.recorded index := by
  cases self with
  | BTree inner action =>
    cases inner <;> cases hwritten <;> rfl
  | Vec inner action =>
    cases inner <;> cases hwritten <;> rfl

end milhouse.cow
