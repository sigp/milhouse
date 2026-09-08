import Tree.Invariants

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- A pending value at a mathematical index, witnessed by a successful lookup
    at the corresponding machine index. -/
def HasValueAt {T U : Type} (mapInst : UpdateMap U T) (updates : U) (index : Nat) : Prop :=
  ∃ (query : Std.Usize) (value : T), query.val = index ∧ mapInst.get updates query = ok (some value)

theorem get_some_of_hasValueAt {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    {query : Std.Usize} (hhas : HasValueAt mapInst updates query.val) :
    ∃ value, mapInst.get updates query = ok (some value) := by
  obtain ⟨actual, value, hindex, hget⟩ := hhas
  have heq : actual = query := UScalar.eq_of_val_eq hindex
  exact ⟨value, by simpa only [heq] using hget⟩

/-- The supplied maximum bounds every pending value. Attainment and the exact
    maximum are not needed to justify skipping a suffix. -/
def MaximumBoundsValues {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) : Prop :=
  ∀ query value, mapInst.get updates query = ok (some value) →
    ∃ last, maximum = some last ∧ query.val ≤ last.val

theorem get_none_of_maximum_before {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    {maximum : Option Std.Usize} {start query : Std.Usize} {pending : Option T}
    (hmaximum : MaximumBoundsValues mapInst updates maximum)
    (hbefore : ∀ last, maximum = some last → last.val < start.val)
    (hquery : start.val ≤ query.val) (hget : mapInst.get updates query = ok pending) :
    pending = none := by
  cases pending with
  | none => rfl
  | some value =>
    obtain ⟨last, hlast, hbound⟩ := hmaximum query value hget
    have hsmall := hbefore last hlast
    omega

end milhouse.update_map

namespace milhouse.tree

/-- A dense extension ends before the first missing pending position at or
    beyond the old length. This is the no-gap fact needed by early exits. -/
theorem DenseUpdateDomain.length_le_of_missing {oldLength newLength start : Nat}
    {hasUpdate : Nat → Prop} (hdomain : DenseUpdateDomain oldLength newLength hasUpdate)
    (hstart : oldLength ≤ start) (hmissing : ¬ hasUpdate start) :
    newLength ≤ start := by
  by_contra hnot
  exact hmissing (hdomain.extension_complete start hstart (by omega))

theorem DenseUpdateDomain.excludes_after_missing {oldLength newLength start query : Nat}
    {hasUpdate : Nat → Prop} (hdomain : DenseUpdateDomain oldLength newLength hasUpdate)
    (hstart : oldLength ≤ start) (hmissing : ¬ hasUpdate start) (hquery : start ≤ query) :
    ¬ hasUpdate query := by
  have hlength := hdomain.length_le_of_missing hstart hmissing
  intro hhas
  have hbound := hdomain.updates_bounded query hhas
  omega

end milhouse.tree
