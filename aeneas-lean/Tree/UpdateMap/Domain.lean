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

/-- Successful lookups reflect the update domain defined by those lookups;
    no independent law about `get` is necessary. -/
theorem get_isSome_iff_hasValueAt {T U : Type}
    {mapInst : UpdateMap U T} {updates : U} {query : Std.Usize} {found : Option T}
    (hget : mapInst.get updates query = ok found) :
    found.isSome = true ↔ HasValueAt mapInst updates query.val := by
  cases found with
  | none =>
    constructor
    · simp
    · intro hhas
      obtain ⟨value, hvalue⟩ := get_some_of_hasValueAt mapInst updates hhas
      rw [hget] at hvalue
      cases hvalue
  | some value =>
    exact ⟨fun _ => ⟨query, value, rfl, hget⟩, fun _ => rfl⟩

/-- Every newly appended position has a pending value. This is the part of
    dense-domain validity used by progressive suffix early exits. -/
def ExtensionComplete {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    (oldLength newLength : Nat) : Prop :=
  ∀ query, oldLength ≤ query.val → query.val < newLength →
    ∃ value, mapInst.get updates query = ok (some value)

theorem extensionComplete_of_denseUpdateDomain {T U : Type}
    (mapInst : UpdateMap U T) (updates : U) {oldLength newLength : Nat}
    (hdomain : tree.DenseUpdateDomain oldLength newLength (HasValueAt mapInst updates)) :
    ExtensionComplete mapInst updates oldLength newLength := by
  intro query hlo hhi
  exact get_some_of_hasValueAt mapInst updates (hdomain.extension_complete query.val hlo hhi)

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

/-- When all pending values lie before a suffix, a complete extension cannot
    run beyond both the old length and that suffix's starting index. -/
theorem ExtensionComplete.length_le_max_of_maximum_before {T U : Type}
    {mapInst : UpdateMap U T} {updates : U} {oldLength : Nat} {newLength start : Std.Usize}
    {maximum : Option Std.Usize}
    (hcomplete : ExtensionComplete mapInst updates oldLength newLength.val)
    (hmaximum : MaximumBoundsValues mapInst updates maximum)
    (hbefore : ∀ last, maximum = some last → last.val < start.val) :
    newLength.val ≤ max oldLength start.val := by
  by_contra hnot
  have hbound : max oldLength start.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
  let query := Std.Usize.ofNatCore (max oldLength start.val) hbound
  have hquery : query.val = max oldLength start.val := Usize.ofNatCore_val_eq hbound
  obtain ⟨value, hget⟩ := hcomplete query (by omega) (by omega)
  have hnone := get_none_of_maximum_before mapInst updates hmaximum hbefore (by omega) hget
  cases hnone

/-- Bounding every pending value is sufficient to bound only the extension
extent. The latter is all that density needs when a maximum skips a suffix;
pending entries already inside the old backing need not satisfy that stronger
semantic bound. A machine-maximal index needs no representable successor. -/
theorem ExtensionComplete.length_le_maximum_extent {T U : Type}
    {mapInst : UpdateMap U T} {updates : U} {oldLength : Nat} {newLength : Std.Usize}
    {maximum : Option Std.Usize}
    (hcomplete : ExtensionComplete mapInst updates oldLength newLength.val)
    (hmaximum : MaximumBoundsValues mapInst updates maximum) :
    newLength.val ≤ maximum.elim oldLength (fun last => max (last.val + 1) oldLength) := by
  cases maximum with
  | none =>
    simpa using hcomplete.length_le_max_of_maximum_before hmaximum
      (start := 0#usize) (by intro last hlast; cases hlast)
  | some last =>
    simp only [Option.elim_some]
    by_cases hroom : last.val < Std.Usize.max
    · have hbound : last.val + 1 < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
      let start := Std.Usize.ofNatCore (last.val + 1) hbound
      have hstart : start.val = last.val + 1 := Usize.ofNatCore_val_eq hbound
      have hlength := hcomplete.length_le_max_of_maximum_before hmaximum
        (start := start) (by intro actual hactual; cases hactual; omega)
      simpa only [hstart, Nat.max_comm] using hlength
    · scalar_tac

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
