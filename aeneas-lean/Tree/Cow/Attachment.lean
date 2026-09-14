import Tree.Cow.Consuming
import Tree.Cow.CallbackAttachment

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- The handle data after attaching another maximum-index borrow, retaining
any existing callbacks on the inner handle. -/
def Cow.attachIndex {T : Type} (self : Cow T) (state : update_map.MaxIndexState)
    (index : Std.Usize) : Cow T :=
  match self with
  | .BTree inner action => .BTree inner (action.attachIndex state index)
  | .Vec inner action => .Vec inner (action.attachIndex state index)

/-- The exact attachment continuation. Compatible handle variants return
their inner data and original callback chain; incompatible variants restore
both original borrows. -/
def Cow.releaseIndex {T : Type} (self : Cow T) (state : update_map.MaxIndexState)
    (replacement : Cow T) : Cow T × update_map.MaxIndexState :=
  match self, replacement with
  | .BTree _ action, .BTree inner next =>
      let (restored, state) := action.releaseIndex state next
      (.BTree inner restored, state)
  | .Vec _ action, .Vec inner next =>
      let (restored, state) := action.releaseIndex state next
      (.Vec inner restored, state)
  | _, _ => (self, state)

/-- Attachment is total and has exactly the extracted backward continuation,
without cloning, entry, or metadata assumptions. -/
theorem Cow.with_max_index_eq {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (state : update_map.MaxIndexState) (index : Std.Usize) :
    Cow.with_max_index cloneInst self state index =
      ok (self.attachIndex state index, self.releaseIndex state) := by
  cases self with
  | BTree inner action =>
    simp! only [Cow.with_max_index, CowOnMut.with_max_index_eq, bind_tc_ok]
    apply congrArg ok
    apply Prod.ext
    · rfl
    · funext replacement
      cases replacement with
      | BTree replacement callback =>
        cases callback
        simp! only [Cow.releaseIndex, CowOnMut.eta]
        cases action.releaseIndex state _ with
        | mk restored next => cases restored; rfl
      | Vec _ _ =>
        cases action with
        | mk action previous => cases action <;> rfl
  | Vec inner action =>
    simp! only [Cow.with_max_index, CowOnMut.with_max_index_eq, bind_tc_ok]
    apply congrArg ok
    apply Prod.ext
    · rfl
    · funext replacement
      cases replacement with
      | BTree _ _ =>
        cases action with
        | mk action previous => cases action <;> rfl
      | Vec replacement callback =>
        cases callback
        simp! only [Cow.releaseIndex, CowOnMut.eta]
        cases action.releaseIndex state _ with
        | mk restored next => cases restored; rfl

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

/-- Metadata attachment leaves the exact structural materialization inputs
unchanged, including a vacant vector entry's representable growth bound. -/
theorem Cow.attachIndex_canMaterialize {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    (self.attachIndex state index).CanMaterialize ↔ self.CanMaterialize := by
  cases self with
  | BTree inner action =>
    cases inner with
    | Mutable _ => rfl
    | Immutable _ entry => cases entry <;> rfl
  | Vec inner action =>
    cases inner with
    | Mutable _ => rfl
    | Immutable _ entry => cases entry <;> rfl

/-- Releasing the attached handle unchanged restores both original borrows. -/
theorem Cow.releaseIndex_attachIndex {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) :
    self.releaseIndex state (self.attachIndex state index) = (self, state) := by
  cases self <;> simp [Cow.releaseIndex, Cow.attachIndex, CowOnMut.releaseIndex_attachIndex]

/-- Attaching maximum-index tracking changes no carried value. Releasing the
attached handle unchanged restores the exact original handle and maximum. -/
theorem Cow.with_max_index_roundtrip {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (state : update_map.MaxIndexState) (index : Std.Usize) :
    ∃ attached back,
      Cow.with_max_index cloneInst self state index = ok (attached, back) ∧
      attached.value = self.value ∧ attached.onMut.max_index = some (state, index) ∧
      back attached = (self, state) := by
  refine ⟨self.attachIndex state index, self.releaseIndex state,
    Cow.with_max_index_eq cloneInst self state index,
    Cow.attachIndex_value self state index, ?_, Cow.releaseIndex_attachIndex self state index⟩
  cases self <;> rfl

/-- Every filled footprint records the outer key, independently of inner-map
laws, cloning, index bounds, or the existing callback chain. -/
theorem Cow.releaseIndex_written_maximum {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) (replacement : T)
    {changed : Cow T}
    (hwritten : (self.attachIndex state index).Written replacement changed) :
    (self.releaseIndex state changed).2 = state.recorded index := by
  cases self with
  | BTree inner action =>
    cases inner <;> cases hwritten <;>
      simp [Cow.releaseIndex, CowOnMut.releaseIndex_recorded_attachIndex]
  | Vec inner action =>
    cases inner <;> cases hwritten <;>
      simp [Cow.releaseIndex, CowOnMut.releaseIndex_recorded_attachIndex]

/-- Returning a filled outer handle now supplies the original inner handle's
complete Written footprint, including every existing callback. No callback-
neutrality or map-metadata assumption is required. -/
theorem Cow.releaseIndex_written {T : Type} (self : Cow T)
    (state : update_map.MaxIndexState) (index : Std.Usize) (replacement : T)
    {changed : Cow T}
    (hwritten : (self.attachIndex state index).Written replacement changed) :
    self.Written replacement (self.releaseIndex state changed).1 := by
  cases self with
  | BTree inner action =>
    cases inner <;> cases hwritten <;>
      simp only [Cow.releaseIndex, CowOnMut.releaseIndex_recorded_attachIndex] <;>
      constructor
  | Vec inner action =>
    cases inner <;> cases hwritten <;>
      simp only [Cow.releaseIndex, CowOnMut.releaseIndex_recorded_attachIndex] <;>
      constructor
    assumption

end milhouse.cow
