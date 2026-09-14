import Tree.ProgressiveList.Push.State

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- With a returned map maximum, push succeeds exactly when its mathematical
merged length is below the machine limit, provided the one reached insertion
terminates. No indexed reads, representation, packing, cloning, or laws about
the inserted map are needed to characterize execution success. -/
theorem ProgressiveList.push_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest)
    (hinsert : ∀ index : Std.Usize,
      index.val = largest.elim self.length.val (fun last => max (last.val + 1) self.length.val) →
      index.val < Std.Usize.max →
      ∃ previous updates, mapInst.insert self.updates index value = ok (previous, updates)) :
    (∃ result, ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), result)) ↔
      largest.elim self.length.val (fun last => max (last.val + 1) self.length.val) < Std.Usize.max := by
  constructor
  · rintro ⟨result, hpush⟩
    cases hlen : ProgressiveList.len ValueInst mapInst self with
    | fail e => simp [ProgressiveList.push, hlen] at hpush
    | div => simp [ProgressiveList.push, hlen] at hpush
    | ok index =>
      have hnotFull : index ≠ core.num.Usize.MAX := by
        intro heq
        rw [heq] at hlen
        rw [ProgressiveList.push_full ValueInst mapInst self value hlen] at hpush
        cases hpush
      have hbound := (ProgressiveList.len_success_iff ValueInst mapInst self largest hmax).mp
        ⟨index, hlen⟩
      obtain ⟨actual, hactual, hvalue⟩ := ProgressiveList.len_total_spec
        ValueInst mapInst self largest hmax hbound
      rw [hlen] at hactual
      cases hactual
      scalar_tac
  · intro hroom
    have hbound : ∀ last, largest = some last → last.val < Std.Usize.max := by
      intro last hlast
      rw [hlast] at hroom
      simp only [Option.elim_some] at hroom
      omega
    obtain ⟨index, hlen, hvalue⟩ := ProgressiveList.len_total_spec
      ValueInst mapInst self largest hmax hbound
    have hindex : index.val < Std.Usize.max := by omega
    obtain ⟨previous, updates, hins⟩ := hinsert index hvalue hindex
    exact ⟨{ self with updates := updates },
      ProgressiveList.push_succeeds ValueInst mapInst self value index hlen (by scalar_tac) hins⟩

/-- `ListFull` is returned precisely when the mathematical merged length is
the machine maximum. Insertion need not terminate, since this branch never
calls it. An overflowing maximum-index successor lies above that length and
is not silently classified as a returned `ListFull` error. -/
theorem ProgressiveList.push_full_iff_of_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest) :
    ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Err (.ListFull core.num.Usize.MAX), self) ↔
      largest.elim self.length.val (fun last => max (last.val + 1) self.length.val) = Std.Usize.max := by
  rw [ProgressiveList.push_error_iff_full]
  simp only [and_true]
  constructor
  · intro hlen
    have hbound := (ProgressiveList.len_success_iff ValueInst mapInst self largest hmax).mp
      ⟨core.num.Usize.MAX, hlen⟩
    obtain ⟨actual, hactual, hvalue⟩ := ProgressiveList.len_total_spec
      ValueInst mapInst self largest hmax hbound
    rw [hlen] at hactual
    cases hactual
    scalar_tac
  · intro hfull
    have hbound : ∀ last, largest = some last → last.val < Std.Usize.max := by
      intro last hlast
      rw [hlast] at hfull
      simp only [Option.elim_some] at hfull
      omega
    obtain ⟨index, hlen, hvalue⟩ := ProgressiveList.len_total_spec
      ValueInst mapInst self largest hmax hbound
    have heq : index = core.num.Usize.MAX := by scalar_tac
    simpa only [heq] using hlen

end milhouse.progressive_list
