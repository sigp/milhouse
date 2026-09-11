import Tree.Funs

open Aeneas Aeneas.Std Result

namespace milhouse.update_map

/-- Exact agreement of raw lookup outcomes when a missing entry delegates to
the same fallback. A present entry may replace an absent one precisely when
the fallback supplies that value. Failures and divergence remain observable. -/
def LookupResultsAgree {T : Type} (fallback : Result (Option T)) :
    Result (Option T) → Result (Option T) → Prop
  | ok none, ok none => True
  | ok none, right => fallback = right
  | left, ok none => left = fallback
  | left, right => left = right

theorem LookupResultsAgree.refl {T : Type}
    (fallback result : Result (Option T)) : LookupResultsAgree fallback result result := by
  cases result with
  | ok value => cases value <;> simp [LookupResultsAgree]
  | fail error | div => rfl

/-- Exact map-read equality always implies agreement after the fallback. -/
theorem LookupResultsAgree.of_eq {T : Type}
    (fallback : Result (Option T)) {left right : Result (Option T)} (heq : left = right) :
    LookupResultsAgree fallback left right := by
  rw [heq]
  exact LookupResultsAgree.refl fallback right

/-- An absent and a present entry can agree without equal raw map answers. -/
theorem LookupResultsAgree.none_some_iff {T : Type}
    (fallback : Result (Option T)) (value : T) :
    LookupResultsAgree fallback (ok none) (ok (some value)) ↔ fallback = ok (some value) := Iff.rfl

/-- Resolving missing entries against the fallback gives the same complete
result exactly under the raw-outcome relation. Neither query nor fallback is
assumed to succeed. This is a proof equation, not a replacement map model. -/
theorem lookup_with_fallback_eq_iff {T : Type}
    (fallback left right : Result (Option T)) :
    (do let value ← left; value.elim fallback (fun item => ok (some item))) =
      (do let value ← right; value.elim fallback (fun item => ok (some item))) ↔
        LookupResultsAgree fallback left right := by
  cases left with
  | ok left =>
    cases left <;> cases right with
    | ok right => cases right <;> simp [LookupResultsAgree]
    | fail error | div => simp [LookupResultsAgree]
  | fail error | div =>
    cases right with
    | ok right => cases right <;> simp [LookupResultsAgree]
    | fail error | div => simp [LookupResultsAgree]

end milhouse.update_map
