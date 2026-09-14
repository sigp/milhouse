import Tree.Funs

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- Every element `ne` call reached by the short-circuit loop terminates.
A true result stops immediately, leaving the remaining pairs unconstrained.
This describes external element calls, not an assumed vector or rebase result. -/
def NeComparisons {T U : Type} (inst : core.cmp.PartialEq T U) : _root_.List (T × U) → Prop
  | [] => True
  | pair :: rest => ∃ different, inst.ne pair.1 pair.2 = ok different ∧
      (different = false → NeComparisons inst rest)

/-- Termination for all paired inputs supplies the weaker short-circuit law. -/
theorem neComparisons_of_pairs {T U : Type} (inst : core.cmp.PartialEq T U)
    (pairs : _root_.List (T × U))
    (hne : ∀ pair ∈ pairs, ∃ different, inst.ne pair.1 pair.2 = ok different) :
    NeComparisons inst pairs := by
  induction pairs with
  | nil => trivial
  | cons pair rest ih =>
    obtain ⟨different, hcall⟩ := hne pair (by simp)
    exact ⟨different, hcall, fun _ => ih (fun item hitem => hne item (by simp [hitem]))⟩

/-- The reached element-call law suffices for the actual external comparison
loop to return, without requiring any call after the first true `ne`. -/
theorem NeComparisons.anyM_success {T U : Type} {inst : core.cmp.PartialEq T U}
    {pairs : _root_.List (T × U)} (hne : NeComparisons inst pairs) :
    ∃ different, _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) pairs = ok different := by
  induction pairs with
  | nil => exact ⟨false, rfl⟩
  | cons pair rest ih =>
    obtain ⟨different, hcall, hrest⟩ := hne
    cases different with
    | true => exact ⟨true, by simp [hcall, pure]⟩
    | false =>
      obtain ⟨different, htail⟩ := ih (hrest rfl)
      exact ⟨different, by simp [hcall, htail]⟩

/-- Every successful execution supplies the reached-call law, so the scope
does not demand terminating comparisons omitted by the real loop. -/
theorem neComparisons_of_anyM_success {T U : Type} {inst : core.cmp.PartialEq T U}
    {pairs : _root_.List (T × U)} {different : Bool}
    (hsuccess : _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) pairs = ok different) :
    NeComparisons inst pairs := by
  induction pairs generalizing different with
  | nil => trivial
  | cons pair rest ih =>
    cases hcall : inst.ne pair.1 pair.2 with
    | fail error => simp [hcall] at hsuccess
    | div => simp [hcall] at hsuccess
    | ok headDifferent =>
      refine ⟨headDifferent, hcall, ?_⟩
      intro hfalse
      subst headDifferent
      exact ih (by simpa [hcall] using hsuccess)

end milhouse_models
