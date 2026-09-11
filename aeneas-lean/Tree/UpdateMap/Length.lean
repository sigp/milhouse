import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.utils

/-- The nonempty-map branch performs checked addition before taking the
    maximum with the backing length. Keeping this equation in `Result`
    preserves the overflow behavior instead of assuming it away. -/
theorem updated_length_of_max_index {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (index : Std.Usize) (hmax : mapInst.max_index updates = ok (some index)) :
    updated_length mapInst previous updates = (do
      let next ← index + 1#usize
      ok (core.cmp.impls.OrdUsize.max next previous)) := by
  simp [updated_length, hmax, core.option.Option.map_or,
    updated_length.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeLength.call_once,
    Length.as_usize, liftFun2]

/-- A successful length calculation has exactly the mathematical value
    `max (largest update index + 1) backing_length`. Success supplies the
    overflow check, so no separate arithmetic bounds are assumptions. -/
theorem updated_length_max_spec {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (index length : Std.Usize)
    (hmax : mapInst.max_index updates = ok (some index))
    (hlen : updated_length mapInst previous updates = ok length) :
    length.val = max (index.val + 1) previous.val := by
  rw [updated_length_of_max_index mapInst previous updates index hmax] at hlen
  cases hnext : index + 1#usize with
  | fail e => simp [hnext] at hlen
  | div => simp [hnext] at hlen
  | ok next =>
    simp only [hnext, bind_tc_ok, ok.injEq] at hlen
    have hnext_val : next.val = index.val + 1 := by
      have h := UScalar.add_equiv index 1#usize
      rw [hnext] at h
      simp at h
      omega
    rw [← hlen]
    simp [hnext_val]

/-- Computing the merged length never shortens the backing sequence. -/
theorem updated_length_ge_backing {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (length : Std.Usize)
    (hlen : updated_length mapInst previous updates = ok length) :
    previous.val ≤ length.val := by
  cases hmax : mapInst.max_index updates with
  | fail e => simp [updated_length, hmax] at hlen
  | div => simp [updated_length, hmax] at hlen
  | ok largest =>
    cases largest with
    | none =>
      simp [updated_length, hmax, core.option.Option.map_or] at hlen
      subst length
      exact Nat.le_refl _
    | some index =>
      rw [updated_length_max_spec mapInst previous updates index length hmax hlen]
      exact Nat.le_max_right _ _

/-- Length calculation succeeds whenever the largest update index has a
    representable successor. The maximum cannot itself overflow because its
    other argument is already a machine-sized backing length. -/
theorem updated_length_succeeds {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (index : Std.Usize)
    (hmax : mapInst.max_index updates = ok (some index))
    (hbound : index.val < Std.Usize.max) :
    ∃ length, updated_length mapInst previous updates = ok length ∧
      length.val = max (index.val + 1) previous.val := by
  have hs := Std.Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac)
  cases hnext : index + 1#usize with
  | fail e => rw [hnext] at hs; simp at hs
  | div => rw [hnext] at hs; simp at hs
  | ok next =>
    have hlen : updated_length mapInst previous updates =
        ok (core.cmp.impls.OrdUsize.max next previous) := by
      rw [updated_length_of_max_index mapInst previous updates index hmax]
      simp [hnext]
    exact ⟨_, hlen, updated_length_max_spec mapInst previous updates index _ hmax hlen⟩

/-- Exact total merged-length calculation from the actual optional maximum.
Only a present maximum needs a representable successor; no map-read or
representation law is needed by this metadata computation. -/
theorem updated_length_total_spec {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (largest : Option Std.Usize) (hmax : mapInst.max_index updates = ok largest)
    (hbound : ∀ index, largest = some index → index.val < Std.Usize.max) :
    ∃ length, updated_length mapInst previous updates = ok length ∧
      length.val = largest.elim previous.val (fun index => max (index.val + 1) previous.val) := by
  cases largest with
  | none =>
    exact ⟨previous, by simp [updated_length, hmax, core.option.Option.map_or], rfl⟩
  | some index =>
    exact updated_length_succeeds mapInst previous updates index hmax (hbound index rfl)

/-- Exact successful length criterion from the raw maximum query. The target
machine length supplies successor representability, so neither a separate
overflow bound nor any map-read or validity law is needed. -/
theorem updated_length_eq_ok_iff {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (length : Std.Usize) :
    updated_length mapInst previous updates = ok length ↔
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim previous.val (fun index => max (index.val + 1) previous.val) = length.val := by
  constructor
  · intro hlength
    cases hmax : mapInst.max_index updates with
    | fail error | div => simp [updated_length, hmax] at hlength
    | ok largest =>
      refine ⟨largest, rfl, ?_⟩
      cases largest with
      | none =>
        have heq : previous = length := by
          simpa [updated_length, hmax, core.option.Option.map_or] using hlength
        simp [heq]
      | some index =>
        exact (updated_length_max_spec mapInst previous updates index length hmax hlength).symm
  · rintro ⟨largest, hmax, hextent⟩
    have hbound : ∀ index, largest = some index → index.val < Std.Usize.max := by
      intro index hindex
      rw [hindex] at hextent
      simp only [Option.elim_some] at hextent
      scalar_tac
    obtain ⟨computed, hcomputed, hvalue⟩ :=
      updated_length_total_spec mapInst previous updates largest hmax hbound
    have heq : computed = length := by
      apply UScalar.eq_of_val_eq
      exact hvalue.trans hextent
    simpa only [heq] using hcomputed

/-- To extend strictly beyond the backing sequence to `index + 1`, the raw
maximum must be exactly `index`, and its successor must fit. There is no
freedom to change the maximum while retaining this larger logical extent. -/
theorem updated_length_succ_iff_max_index {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (index : Std.Usize) (hbacking : previous.val ≤ index.val) :
    (∃ length, updated_length mapInst previous updates = ok length ∧
      length.val = index.val + 1) ↔
      index.val < Std.Usize.max ∧ mapInst.max_index updates = ok (some index) := by
  constructor
  · rintro ⟨length, hlength, hvalue⟩
    have hbound : index.val < Std.Usize.max := by scalar_tac
    obtain ⟨largest, hmax, hextent⟩ :=
      (updated_length_eq_ok_iff mapInst previous updates length).mp hlength
    refine ⟨hbound, ?_⟩
    cases largest with
    | none => simp only [Option.elim_none] at hextent; omega
    | some largest =>
      have heq : largest = index := by
        apply UScalar.eq_of_val_eq
        simp only [Option.elim_some] at hextent
        omega
      simpa only [heq] using hmax
  · rintro ⟨hbound, hmax⟩
    obtain ⟨length, hlength, hvalue⟩ :=
      updated_length_succeeds mapInst previous updates index hmax hbound
    exact ⟨length, hlength, by omega⟩

/-- With a returned map maximum, successor representability is both necessary
and sufficient for the actual length computation to succeed. -/
theorem updated_length_success_iff {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (largest : Option Std.Usize) (hmax : mapInst.max_index updates = ok largest) :
    (∃ length, updated_length mapInst previous updates = ok length) ↔
      ∀ index, largest = some index → index.val < Std.Usize.max := by
  constructor
  · rintro ⟨length, hlength⟩ index hindex
    have hvalue := updated_length_max_spec mapInst previous updates index length
      (by simpa only [hindex] using hmax) hlength
    scalar_tac
  · intro hbound
    obtain ⟨length, hlength, _⟩ := updated_length_total_spec mapInst previous updates largest hmax hbound
    exact ⟨length, hlength⟩

/-- Recording an inserted key below the current logical end preserves merged
    length. The metadata law describes maximum-index insertion, independently
    of how the new map was produced (push, mutable access, or CoW write-back). -/
theorem updated_length_insert_below {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates updated : U)
    (index length : Std.Usize)
    (hlen : updated_length mapInst previous updates = ok length)
    (hindex : index.val < length.val)
    (hmax : ∀ oldMax, mapInst.max_index updates = ok oldMax →
      mapInst.max_index updated = ok (some (oldMax.elim index
        (core.cmp.impls.OrdUsize.max index)))) :
    updated_length mapInst previous updated = ok length := by
  cases hold : mapInst.max_index updates with
  | fail e => simp [updated_length, hold] at hlen
  | div => simp [updated_length, hold] at hlen
  | ok oldMax =>
    have hnew := hmax oldMax hold
    cases oldMax with
    | none =>
      simp only [Option.elim_none] at hnew
      have hlength : length = previous := by
        simpa [updated_length, hold, core.option.Option.map_or] using hlen.symm
      obtain ⟨newLength, hnewLength, hval⟩ :=
        updated_length_succeeds mapInst previous updated index hnew (by scalar_tac)
      have heq : newLength = length := by
        rw [hlength] at hindex ⊢
        scalar_tac
      rwa [heq] at hnewLength
    | some oldIndex =>
      simp only [Option.elim_some] at hnew
      have hlength := updated_length_max_spec mapInst previous updates oldIndex length hold hlen
      have hnewMax : (core.cmp.impls.OrdUsize.max index oldIndex).val =
          max index.val oldIndex.val := by simp
      obtain ⟨newLength, hnewLength, hval⟩ :=
        updated_length_succeeds mapInst previous updated
          (core.cmp.impls.OrdUsize.max index oldIndex) hnew (by scalar_tac)
      have heq : newLength = length := by scalar_tac
      rwa [heq] at hnewLength

end milhouse.utils
