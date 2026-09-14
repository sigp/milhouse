import Tree.ProgressiveList.Length

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A returned iterator-construction error is exactly the bounds error for
the observed logical length. Neither direction needs a backing invariant,
packing law, indexed-read law, or successful unchecked constructor. -/
theorem ProgressiveList.iter_from_error_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {err : error.Error} :
    ProgressiveList.iter_from ValueInst mapInst self index = ok (core.result.Result.Err err) ↔
      ∃ length, ProgressiveList.len ValueInst mapInst self = ok length ∧
        length.val < index.val ∧ err = .OutOfBoundsIterFrom index length := by
  constructor
  · intro hiter
    cases hlen : ProgressiveList.len ValueInst mapInst self with
    | fail e => simp [ProgressiveList.iter_from, hlen] at hiter
    | div => simp [ProgressiveList.iter_from, hlen] at hiter
    | ok length =>
      by_cases houtside : index > length
      · simp only [ProgressiveList.iter_from, hlen, bind_tc_ok, if_pos houtside,
          ok.injEq, core.result.Result.Err.injEq] at hiter
        exact ⟨length, rfl, by scalar_tac, hiter.symm⟩
      · simp only [ProgressiveList.iter_from, hlen, bind_tc_ok, if_neg houtside] at hiter
        cases hfrom : ProgressiveList.iter_from_unchecked ValueInst mapInst self index <;>
          simp [hfrom] at hiter
  · rintro ⟨length, hlen, hindex, rfl⟩
    have houtside : index > length := by scalar_tac
    simp only [ProgressiveList.iter_from, hlen, bind_tc_ok, if_pos houtside]

/-- Oversized starts return the exact bounds error directly from the actual
optional map maximum. The oversized-index comparison supplies the successor
bound and length calculation; no separate length-success, sequence-read,
representation, or backing premise is needed. -/
theorem ProgressiveList.iter_from_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest)
    (hindex : largest.elim self.length.val
      (fun last => max (last.val + 1) self.length.val) < index.val) :
    ∃ length : Std.Usize,
      length.val = largest.elim self.length.val (fun last => max (last.val + 1) self.length.val) ∧
      ProgressiveList.iter_from ValueInst mapInst self index =
        ok (core.result.Result.Err (.OutOfBoundsIterFrom index length)) := by
  have hbound : ∀ last, largest = some last → last.val < Std.Usize.max := by
    intro last hlast
    rw [hlast] at hindex
    simp only [Option.elim_some] at hindex
    scalar_tac
  obtain ⟨length, hlen, hvalue⟩ := ProgressiveList.len_total_spec
    ValueInst mapInst self largest hmax hbound
  exact ⟨length, hvalue, (ProgressiveList.iter_from_error_iff ValueInst mapInst self index).mpr
    ⟨length, hlen, by omega, rfl⟩⟩

end milhouse.progressive_list
