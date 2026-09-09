import Tree.ProgressiveList.Length

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Pushing a full list returns `ListFull` and leaves the complete state
    unchanged, without evaluating map insertion. -/
theorem ProgressiveList.push_full {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok core.num.Usize.MAX) :
    ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Err (.ListFull core.num.Usize.MAX), self) := by
  simp [ProgressiveList.push, hlen]

/-- The only explicit rejection in `push` is a full logical length; when
    length evaluation and insertion succeed below that limit, push succeeds. -/
theorem ProgressiveList.push_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) (index : Std.Usize)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok index)
    (hroom : index ≠ core.num.Usize.MAX) {previous : Option T} {updates : U}
    (hinsert : mapInst.insert self.updates index value = ok (previous, updates)) :
    ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), { self with updates := updates }) := by
  simp only [ProgressiveList.push, hlen, bind_tc_ok, if_neg hroom, hinsert]
  rfl

/-- After a successful push, increasing logical length by exactly one is
equivalent to the returned map reporting the appended index as its maximum.
Unlike writes within the existing length, this strictly larger extent fixes
the maximum uniquely. Success supplies every capacity bound. -/
theorem ProgressiveList.len_after_push_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) (index : Std.Usize)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok index)
    {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    (∃ length, ProgressiveList.len ValueInst mapInst pushed = ok length ∧
      length.val = index.val + 1) ↔ mapInst.max_index pushed.updates = ok (some index) := by
  have hroom : index ≠ core.num.Usize.MAX := by
    intro hfull
    subst index
    rw [ProgressiveList.push_full ValueInst mapInst self value hlen] at hpush
    cases hpush
  have hbound : index.val < Std.Usize.max := by scalar_tac
  have hbacking := ProgressiveList.len_ge_backing ValueInst mapInst self index hlen
  obtain ⟨_, updates, _, rfl⟩ :=
    ProgressiveList.push_success ValueInst mapInst self value index hlen hpush
  simpa only [ProgressiveList.len_eq_updated_length, hbound, true_and] using
    utils.updated_length_succ_iff_max_index mapInst self.length updates index hbacking

/-- A successful push increases logical length by exactly one. The map law
    states that insertion at the old logical end makes that index the map's
    maximum. This is the only metadata law needed; the old length and the
    success result supply the backing-length and overflow bounds. -/
theorem ProgressiveList.len_after_push {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) (index : Std.Usize)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok index)
    (hinsert_max : ∀ previous updates,
      mapInst.insert self.updates index value = ok (previous, updates) →
      mapInst.max_index updates = ok (some index))
    {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    ∃ length, ProgressiveList.len ValueInst mapInst pushed = ok length ∧
      length.val = index.val + 1 := by
  apply (ProgressiveList.len_after_push_iff_max_index ValueInst mapInst self value index hlen hpush).mpr
  obtain ⟨previous, updates, hins, rfl⟩ :=
    ProgressiveList.push_success ValueInst mapInst self value index hlen hpush
  exact hinsert_max previous updates hins

end milhouse.progressive_list
