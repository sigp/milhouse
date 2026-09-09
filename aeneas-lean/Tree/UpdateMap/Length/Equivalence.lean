import Tree.UpdateMap.Length

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.utils

/-- The mathematical extent described by successful maximum metadata. -/
def maxIndexExtent (previous : Length) (largest : Option Std.Usize) : Nat :=
  largest.elim previous.val (fun index => max (index.val + 1) previous.val)

/-- Exact agreement of maximum-query results as observed by length. Successful
queries may return different maxima with the same mathematical extent. The
one overflowing index also agrees with an explicit integer-overflow failure;
other errors and divergence must agree. No map or length call is assumed. -/
def MaxIndexResultsAgree (previous : Length) :
    Result (Option Std.Usize) → Result (Option Std.Usize) → Prop
  | ok left, ok right => maxIndexExtent previous left = maxIndexExtent previous right
  | fail left, fail right => left = right
  | div, div => True
  | fail error, ok (some index) | ok (some index), fail error =>
      error = Error.integerOverflow ∧ index.val = Std.Usize.max
  | _, _ => False

theorem MaxIndexResultsAgree.refl (previous : Length) (result : Result (Option Std.Usize)) :
    MaxIndexResultsAgree previous result result := by
  cases result <;> simp [MaxIndexResultsAgree]

/-- An absent maximum and a present maximum give the same length exactly
when the present update lies within the recorded backing sequence. -/
theorem MaxIndexResultsAgree.none_some_iff (previous : Length) (index : Std.Usize) :
    MaxIndexResultsAgree previous (ok none) (ok (some index)) ↔ index.val < previous.val := by
  simp only [MaxIndexResultsAgree, maxIndexExtent, Option.elim_none, Option.elim_some]
  omega

private theorem tryMk_value (value : Std.Usize) :
    UScalar.tryMk .Usize value.val = ok value := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, value.hBounds,
    decide_true, ↓reduceDIte, Result.ofOption]
  congr 1

private theorem tryMk_eq_fail_iff (n : Nat) (error : Error) :
    UScalar.tryMk .Usize n = fail error ↔ Std.Usize.max < n ∧ error = Error.integerOverflow := by
  by_cases h : n < 2 ^ System.Platform.numBits
  · have hn : ¬ Std.Usize.max < n := by scalar_tac
    simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption, hn]
  · have hn : Std.Usize.max < n := by scalar_tac
    simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption, hn, eq_comm]

private theorem tryMk_ne_div (n : Nat) : UScalar.tryMk .Usize n ≠ div := by
  cases h : UScalar.tryMkOpt .Usize n <;> simp [UScalar.tryMk, h, Result.ofOption]

private theorem tryMk_of_bound (n : Nat) (h : n ≤ Std.Usize.max) :
    ∃ value, UScalar.tryMk .Usize n = ok value ∧ value.val = n := by
  cases hr : UScalar.tryMk .Usize n with
  | fail e => have := (tryMk_eq_fail_iff n e).mp hr; omega
  | div => exact False.elim (tryMk_ne_div n hr)
  | ok value =>
    have hv := UScalar.tryMk_eq .Usize n
    simp only [hr] at hv
    exact ⟨value, rfl, hv.1⟩

private theorem tryMk_eq_iff {left right : Nat}
    (hl : left ≤ Std.Usize.max + 1) (hr : right ≤ Std.Usize.max + 1) :
    UScalar.tryMk .Usize left = UScalar.tryMk .Usize right ↔ left = right := by
  by_cases hleft : left ≤ Std.Usize.max
  · obtain ⟨lv, hlv, hlval⟩ := tryMk_of_bound left hleft
    by_cases hright : right ≤ Std.Usize.max
    · obtain ⟨rv, hrv, hrval⟩ := tryMk_of_bound right hright
      rw [hlv, hrv, ok.injEq]
      constructor
      · intro heq
        simpa only [hlval, hrval] using congrArg UScalar.val heq
      · intro heq
        apply UScalar.eq_of_val_eq
        simpa only [hlval, hrval] using heq
    · have hfail := (tryMk_eq_fail_iff right Error.integerOverflow).mpr ⟨by omega, rfl⟩
      rw [hlv, hfail]
      simp only [reduceCtorEq, false_iff]
      omega
  · by_cases hright : right ≤ Std.Usize.max
    · obtain ⟨rv, hrv, _⟩ := tryMk_of_bound right hright
      have hfail := (tryMk_eq_fail_iff left Error.integerOverflow).mpr ⟨by omega, rfl⟩
      rw [hfail, hrv]
      simp only [reduceCtorEq, false_iff]
      omega
    · have heq : left = right := by omega
      simp only [heq]

private theorem maxIndexExtent_bound (previous : Length) (largest : Option Std.Usize) :
    maxIndexExtent previous largest ≤ Std.Usize.max + 1 := by
  cases largest <;> simp only [maxIndexExtent, Option.elim_none, Option.elim_some] <;> scalar_tac

private theorem maxIndexExtent_overflow_iff (previous : Length) (largest : Option Std.Usize) :
    Std.Usize.max < maxIndexExtent previous largest ↔
      largest.elim False (fun index => index.val = Std.Usize.max) := by
  cases largest <;> simp only [maxIndexExtent, Option.elim_none, Option.elim_some] <;> scalar_tac

private def maximumLength (previous : Length) (result : Result (Option Std.Usize)) : Result Std.Usize := do
  let largest ← result
  UScalar.tryMk .Usize (maxIndexExtent previous largest)

private theorem maximumLength_eq_iff (previous : Length) (left right : Result (Option Std.Usize)) :
    maximumLength previous left = maximumLength previous right ↔ MaxIndexResultsAgree previous left right := by
  cases left with
  | ok left =>
    cases right with
    | ok right =>
      exact tryMk_eq_iff (maxIndexExtent_bound previous left) (maxIndexExtent_bound previous right)
    | fail e =>
      cases left <;> simp [maximumLength, MaxIndexResultsAgree, tryMk_eq_fail_iff,
        maxIndexExtent_overflow_iff, and_comm]
    | div => cases left <;> simp [maximumLength, MaxIndexResultsAgree, tryMk_ne_div]
  | fail e =>
    cases right with
    | ok right =>
      change (fail e = UScalar.tryMk .Usize (maxIndexExtent previous right)) ↔ _
      rw [eq_comm]
      cases right <;> simp [MaxIndexResultsAgree,
        tryMk_eq_fail_iff, maxIndexExtent_overflow_iff, and_comm]
    | fail e1 => simp [maximumLength, MaxIndexResultsAgree]
    | div => simp [maximumLength, MaxIndexResultsAgree]
  | div =>
    cases right with
    | ok right =>
      change (div = UScalar.tryMk .Usize (maxIndexExtent previous right)) ↔ _
      rw [eq_comm]
      cases right <;> simp [MaxIndexResultsAgree, tryMk_ne_div]
    | fail e => simp [maximumLength, MaxIndexResultsAgree]
    | div => simp [maximumLength, MaxIndexResultsAgree]

private theorem updated_length_eq_maximumLength {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U) :
    updated_length mapInst previous updates = maximumLength previous (mapInst.max_index updates) := by
  cases hm : mapInst.max_index updates with
  | fail e => simp [updated_length, maximumLength, hm]
  | div => simp [updated_length, maximumLength, hm]
  | ok largest =>
    cases largest with
    | none => simp [updated_length, maximumLength, hm, core.option.Option.map_or,
        maxIndexExtent, tryMk_value]
    | some index =>
      rw [updated_length_of_max_index mapInst previous updates index hm]
      by_cases hbound : index.val < Std.Usize.max
      · obtain ⟨next, hnext, hval⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have hv : (core.cmp.impls.OrdUsize.max next previous).val =
            max (index.val + 1) previous.val := by simp [hval]
        simp only [hnext, bind_tc_ok, maximumLength, maxIndexExtent, Option.elim_some]
        rw [← hv, tryMk_value]
      · have hindex : index.val = Std.Usize.max := by scalar_tac
        have hnext : index + 1#usize = fail Error.integerOverflow := by
          change UScalar.tryMk .Usize (index.val + (1#usize).val) = fail Error.integerOverflow
          apply (tryMk_eq_fail_iff _ _).mpr
          exact ⟨by scalar_tac, rfl⟩
        have hlength : UScalar.tryMk .Usize (maxIndexExtent previous (some index)) =
            fail Error.integerOverflow := by
          rw [tryMk_eq_fail_iff, maxIndexExtent_overflow_iff]
          exact ⟨hindex, rfl⟩
        simp only [hnext, bind_tc_fail, maximumLength, bind_tc_ok, hlength]

/-- Agreement of the raw maximum-query outcomes is necessary and sufficient
for equal complete length results. This includes callback errors, divergence,
and checked successor overflow; neither map is assumed to be well formed. -/
theorem updated_length_eq_iff_max_index {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (left right : U) :
    updated_length mapInst previous left = updated_length mapInst previous right ↔
      MaxIndexResultsAgree previous (mapInst.max_index left) (mapInst.max_index right) := by
  rw [updated_length_eq_maximumLength, updated_length_eq_maximumLength, maximumLength_eq_iff]

end milhouse.utils
