import Tree.UpdateMap.Domain

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- A range reported empty excludes every successfully read pending value in
    that range. Bulk content preservation only needs this direction of range
    correctness; positive answers may conservatively visit extra subtrees. -/
def RangeExcludesValues {T U : Type} (mapInst : UpdateMap U T) (updates : U) : Prop :=
  ∀ (lo hi query : Std.Usize) (found : Option T),
    mapInst.has_any_in_range updates lo hi = ok false →
    mapInst.get updates query = ok found →
    lo.val ≤ query.val → query.val < hi.val → found = none

/-- Every successful range answer agrees with the presence of a pending
    value. Density preservation needs positive answers to have witnesses as
    well: visiting an empty zero subtree can produce a noncanonical empty
    packed leaf. The law concerns only answers the map actually returns. -/
def RangeReflectsValues {T U : Type} (mapInst : UpdateMap U T) (updates : U) : Prop :=
  ∀ (lo hi : Std.Usize) (answer : Bool),
    mapInst.has_any_in_range updates lo hi = ok answer →
    (answer = true ↔ ∃ index, lo.val ≤ index ∧ index < hi.val ∧
      HasValueAt mapInst updates index)

theorem RangeReflectsValues.excludesValues {T U : Type}
    {mapInst : UpdateMap U T} {updates : U}
    (h : RangeReflectsValues mapInst updates) : RangeExcludesValues mapInst updates := by
  intro lo hi query found hempty hget hlo hhi
  cases found with
  | none => rfl
  | some value =>
    have htrue := (h lo hi false hempty).mpr
      ⟨query.val, hlo, hhi, query, value, rfl, hget⟩
    cases htrue

end milhouse.update_map
