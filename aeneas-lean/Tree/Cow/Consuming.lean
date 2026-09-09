import Tree.Cow.EntrySuccess
import Tree.Cow.Metadata

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- Metadata returned to the original borrow after materialization. -/
def CowOnMut.recorded (self : CowOnMut) : CowOnMut :=
  { max_index := self.max_index.map (fun (state, index) => (state.recorded index, index)) }

/-- An immutable handle needs an entry, and a vector entry needs a
representable destination slot. Already mutable handles need no entry bound. -/
def Cow.CanMaterialize {T : Type} : Cow T → Prop
  | .BTree (.Immutable _ entry) _ => entry.isSome = true
  | .Vec (.Immutable _ (some entry)) _ => entry.index.val < Std.Usize.max
  | .Vec (.Immutable _ none) _ => False
  | .BTree (.Mutable _) _ | .Vec (.Mutable _) _ => True

/-- Entry location carried by a present handle; mutable handles already have
their destination borrow and need no vacant entry. -/
def Cow.EntryAt {T : Type} (index : Std.Usize) : Cow T → Prop
  | .BTree (.Immutable _ (some entry)) _ => entry.key = index
  | .Vec (.Immutable _ (some entry)) _ => entry.index = index
  | .BTree (.Immutable _ none) _ | .Vec (.Immutable _ none) _ => False
  | .BTree (.Mutable _) _ | .Vec (.Mutable _) _ => True

theorem Cow.EntryAt.canMaterialize {T : Type} {index : Std.Usize} {self : Cow T}
    (hentry : self.EntryAt index) (hindex : index.val < Std.Usize.max) : self.CanMaterialize := by
  cases self with
  | BTree inner action =>
    cases inner with
    | Mutable _ => trivial
    | Immutable _ entry => cases entry <;> simp_all [Cow.EntryAt, Cow.CanMaterialize]
  | Vec inner action =>
    cases inner with
    | Mutable _ => trivial
    | Immutable _ entry => cases entry <;> simp_all [Cow.EntryAt, Cow.CanMaterialize]

def Cow.NeedsClone {T : Type} : Cow T → Bool
  | .BTree (.Immutable _ _) _ | .Vec (.Immutable _ _) _ => true
  | .BTree (.Mutable _) _ | .Vec (.Mutable _) _ => false

/-- Only immutable handles call the element clone. Mutable handles return
their existing value, so no clone law is imposed on that branch. -/
def Cow.MaterializedValue {T : Type} (cloneInst : core.clone.Clone T) : Cow T → T → Prop
  | .BTree (.Immutable original _) _, value | .Vec (.Immutable original _) _, value =>
      cloneInst.clone original = ok value
  | .BTree (.Mutable original) _, value | .Vec (.Mutable original) _, value => value = original

/-- The exact slot and maximum-index effects returned through a consumed
handle's backward continuation. The original immutable fallback is retained
as loan data; the newly stored value resides in its entry footprint. -/
inductive Cow.Written {T : Type} : Cow T → T → Cow T → Prop where
  | btree_immutable (original value : T) (entry) (action : CowOnMut) :
      Written (.BTree (.Immutable original (some entry)) action) value
        (.BTree (.Immutable original (some { entry with value := some value })) action.recorded)
  | btree_mutable (original value : T) (action : CowOnMut) :
      Written (.BTree (.Mutable original) action) value (.BTree (.Mutable value) action.recorded)
  | vec_immutable (original value : T) (entry) (action : CowOnMut) (size : Std.Usize)
      (hsize : size.val = max entry.backingLength.val (entry.index.val + 1)) :
      Written (.Vec (.Immutable original (some entry)) action) value
        (.Vec (.Immutable original (some { entry with backingLength := size, value := some value }))
          action.recorded)
  | vec_mutable (original value : T) (action : CowOnMut) :
      Written (.Vec (.Mutable original) action) value (.Vec (.Mutable value) action.recorded)

/-- Consuming mutation succeeds with the actual clone result, or the existing
mutable value, and every replacement reaches precisely the chosen entry and
records the maximum. No clone identity or unrelated element law is assumed. -/
theorem Cow.into_mut_spec {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (value : T) (hready : self.CanMaterialize)
    (hvalue : self.MaterializedValue cloneInst value) :
    ∃ back, Cow.into_mut cloneInst self = ok (.Ok value, back) ∧
      ∀ replacement, self.Written replacement (back (.Ok replacement)) := by
  cases self with
  | BTree inner action =>
    cases inner with
    | Immutable original entry =>
      cases entry with
      | none => simp [Cow.CanMaterialize] at hready
      | some entry =>
        change cloneInst.clone original = ok value at hvalue
        simp! only [Cow.into_mut, BTreeCow.into_mut_inner, hvalue,
          alloc.collections.btree.map.entry.VacantEntry.insert, CowOnMut.run_eq, bind_tc_ok]
        exact ⟨_, rfl, fun replacement => .btree_immutable original replacement entry action⟩
    | Mutable original =>
      change value = original at hvalue
      subst value
      simp! only [Cow.into_mut, BTreeCow.into_mut_inner, CowOnMut.run_eq, bind_tc_ok]
      exact ⟨_, rfl, fun replacement => .btree_mutable original replacement action⟩
  | Vec inner action =>
    cases inner with
    | Immutable original entry =>
      cases entry with
      | none => cases hready
      | some entry =>
        change cloneInst.clone original = ok value at hvalue
        obtain ⟨size, hinsert, hsize⟩ := milhouse_models.vec_entry_insert_success entry value hready
        simp! only [Cow.into_mut, VecCow.into_mut_inner, hvalue, hinsert, CowOnMut.run_eq, bind_tc_ok]
        exact ⟨_, rfl, fun replacement => .vec_immutable original replacement entry action size hsize⟩
    | Mutable original =>
      change value = original at hvalue
      subst value
      simp! only [Cow.into_mut, VecCow.into_mut_inner, CowOnMut.run_eq, bind_tc_ok]
      exact ⟨_, rfl, fun replacement => .vec_mutable original replacement action⟩

/-- Termination needs a clone only for the carried immutable value. The exact
value returned by that clone is exposed, independently of replacement writes. -/
theorem Cow.into_mut_success {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) (hready : self.CanMaterialize)
    (hclone : self.NeedsClone = true → ∃ value, cloneInst.clone self.value = ok value) :
    ∃ value back, Cow.into_mut cloneInst self = ok (.Ok value, back) ∧
      self.MaterializedValue cloneInst value ∧
      ∀ replacement, self.Written replacement (back (.Ok replacement)) := by
  have hvalue : ∃ value, self.MaterializedValue cloneInst value := by
    cases self with
    | BTree inner action =>
      cases inner with
      | Immutable original entry => exact hclone rfl
      | Mutable original => exact ⟨original, rfl⟩
    | Vec inner action =>
      cases inner with
      | Immutable original entry => exact hclone rfl
      | Mutable original => exact ⟨original, rfl⟩
  obtain ⟨value, hvalue⟩ := hvalue
  obtain ⟨back, hcall, hwrites⟩ := Cow.into_mut_spec cloneInst self value hready hvalue
  exact ⟨value, back, hcall, hvalue, hwrites⟩

/-- Both concrete missing-entry variants reject without cloning or recording
maximum metadata. Every continuation input restores the original handle data. -/
theorem Cow.into_mut_missing_entry {T : Type} (cloneInst : core.clone.Clone T)
    (value : T) (action : CowOnMut) :
    Cow.into_mut cloneInst (.BTree (.Immutable value none) action) =
      ok (.Err error.Error.CowMissingEntry, fun _ => .BTree (.Immutable value none) action) ∧
    Cow.into_mut cloneInst (.Vec (.Immutable value none) action) =
      ok (.Err error.Error.CowMissingEntry, fun _ => .Vec (.Immutable value none) action) := by
  exact ⟨rfl, rfl⟩

end milhouse.cow
