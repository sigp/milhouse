import Tree.ProgressiveList.Push.Maximum
import Tree.ProgressiveList.Push.State

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Complete append correctness, including unchanged full-list rejection.
Representation supplies the actual logical-length calculation. Below the
maximum, only the insertion at that length must terminate, record the new
maximum, and preserve other reads after the actual backing fallback. No
behavior is required of the discarded previous-value result, and full lists
need no insertion law.

The backing tree and its recorded length remain exactly unchanged in either
case. No packing, structural capacity, backing validity, or cloning premise is
needed; existing invariants on those unchanged fields therefore survive. -/
theorem ProgressiveList.push_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (value : T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hinsert : ∀ index : Std.Usize, index.val = contents.length → index.val < Std.Usize.max →
      ∃ previous updates, mapInst.insert self.updates index value = ok (previous, updates) ∧
        mapInst.max_index updates = ok (some index) ∧
        ∀ query, self.AppendReadAgrees ValueInst mapInst updates index value query) :
    ∃ outcome result, ProgressiveList.push ValueInst mapInst self value = ok (outcome, result) ∧
      result.tree = self.tree ∧ result.length = self.length ∧
      match outcome with
      | core.result.Result.Ok () =>
        contents.length < Std.Usize.max ∧
          result.Represents ValueInst mapInst (contents ++ [value])
      | core.result.Result.Err error =>
        contents.length = Std.Usize.max ∧ error = .ListFull core.num.Usize.MAX ∧ result = self := by
  obtain ⟨index, hlen, hcontentlen⟩ := hrep.1
  by_cases hroom : index.val < Std.Usize.max
  · obtain ⟨previous, updates, hins, hmax, hget⟩ := hinsert index hcontentlen hroom
    have hpush := ProgressiveList.push_succeeds ValueInst mapInst self value index hlen
      (by scalar_tac) hins
    have hnewRep := (ProgressiveList.push_represents_append_iff
      ValueInst mapInst self contents value hrep hpush).mpr ⟨index, hcontentlen, hmax, hget⟩
    exact ⟨.Ok (), { self with updates := updates }, hpush, rfl, rfl,
      by omega, hnewRep⟩
  · have hfull : index = core.num.Usize.MAX := by scalar_tac
    have hpush := ProgressiveList.push_full ValueInst mapInst self value
      (by simpa only [hfull] using hlen)
    exact ⟨.Err (.ListFull core.num.Usize.MAX), self, hpush, rfl, rfl,
      by scalar_tac, rfl, rfl⟩

end milhouse.progressive_list
