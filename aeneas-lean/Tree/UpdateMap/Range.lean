import Tree.UpdateMap.Domain

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- A range reported empty excludes every successfully read pending value in
    that range. Bulk content preservation only needs this direction of range
    correctness; positive answers may conservatively visit extra subtrees. -/
def RangeExcludesValuesAt {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    (lo hi : Std.Usize) : Prop :=
  ∀ (query : Std.Usize) (found : Option T),
    mapInst.has_any_in_range updates lo hi = ok false →
    mapInst.get updates query = ok found →
    lo.val ≤ query.val → query.val < hi.val → found = none

/-- Every successful range answer agrees with the presence of a pending
    value. Density preservation needs positive answers to have witnesses as
    well: visiting an empty zero subtree can produce a noncanonical empty
    packed leaf. The law concerns only answers the map actually returns. -/
def RangeReflectsValuesAt {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    (lo hi : Std.Usize) : Prop :=
  ∀ answer : Bool,
    mapInst.has_any_in_range updates lo hi = ok answer →
    (answer = true ↔ ∃ index, lo.val ≤ index ∧ index < hi.val ∧
      HasValueAt mapInst updates index)

theorem RangeReflectsValuesAt.excludesValues {T U : Type}
    {mapInst : UpdateMap U T} {updates : U}
    {lo hi : Std.Usize} (h : RangeReflectsValuesAt mapInst updates lo hi) :
    RangeExcludesValuesAt mapInst updates lo hi := by
  intro query found hempty hget hlo hhi
  cases found with
  | none => rfl
  | some value =>
    have htrue := (h false hempty).mpr
      ⟨query.val, hlo, hhi, query, value, rfl, hget⟩
    cases htrue

/-- The unrestricted exclusion law is the range-local law at every endpoint
pair. Traversal specifications can instead require it only at queried pairs. -/
def RangeExcludesValues {T U : Type} (mapInst : UpdateMap U T) (updates : U) : Prop :=
  ∀ lo hi, RangeExcludesValuesAt mapInst updates lo hi

/-- The unrestricted reflection law, retained for external map instances and
callers that already establish correct answers for every range. -/
def RangeReflectsValues {T U : Type} (mapInst : UpdateMap U T) (updates : U) : Prop :=
  ∀ lo hi, RangeReflectsValuesAt mapInst updates lo hi

theorem RangeReflectsValues.excludesValues {T U : Type}
    {mapInst : UpdateMap U T} {updates : U}
    (h : RangeReflectsValues mapInst updates) : RangeExcludesValues mapInst updates := by
  intro lo hi
  exact (h lo hi).excludesValues

end milhouse.update_map
