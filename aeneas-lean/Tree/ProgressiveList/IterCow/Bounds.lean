import Tree.ProgressiveList.Iter.Bounds

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The CoW constructor returns exactly the same bounds errors as the
read-only constructor. Its error continuation is the constant original list,
regardless of its input. This equivalence assumes no representation, packing,
map, or successful unchecked-construction law. -/
theorem ProgressiveList.iter_cow_from_error_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {err : error.Error}
    {back : core.result.Result (ProgressiveListIterCow T U) error.Error → ProgressiveList T U} :
    ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (core.result.Result.Err err, back) ↔
      ProgressiveList.iter_from ValueInst mapInst self index = ok (core.result.Result.Err err) ∧
        back = fun _ => self := by
  rw [ProgressiveList.iter_from_error_iff]
  constructor
  · intro hiter
    cases hlen : ProgressiveList.len ValueInst mapInst self with
    | fail e => simp [ProgressiveList.iter_cow_from, hlen] at hiter
    | div => simp [ProgressiveList.iter_cow_from, hlen] at hiter
    | ok length =>
      by_cases houtside : index > length
      · simp only [ProgressiveList.iter_cow_from, hlen, bind_tc_ok, if_pos houtside,
          ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at hiter
        exact ⟨⟨length, rfl, by scalar_tac, hiter.1.symm⟩, hiter.2.symm⟩
      · simp only [ProgressiveList.iter_cow_from, hlen, bind_tc_ok, if_neg houtside] at hiter
        cases hfrom : ProgressiveList.iter_cow_from_unchecked ValueInst mapInst self index with
        | fail e => simp [hfrom] at hiter
        | div => simp [hfrom] at hiter
        | ok created =>
          obtain ⟨cursor, restore⟩ := created
          simp [hfrom] at hiter
  · rintro ⟨⟨length, hlen, hindex, herr⟩, hback⟩
    have houtside : index > length := by scalar_tac
    rw [herr, hback]
    simp only [ProgressiveList.iter_cow_from, hlen, bind_tc_ok, if_pos houtside]

/-- Oversized CoW starts return the exact metadata-derived bounds error and
restore the complete list for every continuation input. As with read-only
construction, no sequence reads, backing validity, packing, or separately
assumed logical-length success are required. -/
theorem ProgressiveList.iter_cow_from_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest)
    (hindex : largest.elim self.length.val
      (fun last => max (last.val + 1) self.length.val) < index.val) :
    ∃ length : Std.Usize,
      length.val = largest.elim self.length.val (fun last => max (last.val + 1) self.length.val) ∧
      ProgressiveList.iter_cow_from ValueInst mapInst self index =
        ok (core.result.Result.Err (.OutOfBoundsIterFrom index length), fun _ => self) := by
  obtain ⟨length, hvalue, hfrom⟩ := ProgressiveList.iter_from_out_of_bounds
    ValueInst mapInst self index largest hmax hindex
  exact ⟨length, hvalue,
    (ProgressiveList.iter_cow_from_error_iff ValueInst mapInst self index).mpr ⟨hfrom, rfl⟩⟩

end milhouse.progressive_list
