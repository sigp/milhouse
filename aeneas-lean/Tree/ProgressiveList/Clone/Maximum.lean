import Tree.ProgressiveList.Backing

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Replacing the pending map preserves the represented sequence when its
reads agree and its actual maximum gives the same logical length. The maximum
itself may change below the backing length. Represented contents supply every
successor bound; no successful list-length call is assumed for the new map. -/
theorem ProgressiveList.Represents.with_updates_of_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (updates : U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index updates = ok largest)
    (hget : ∀ query, mapInst.get updates query = mapInst.get self.updates query)
    (hextent : largest.elim self.length.val
      (fun index => max (index.val + 1) self.length.val) = contents.length) :
    ({ self with updates } : ProgressiveList T U).Represents ValueInst mapInst contents := by
  obtain ⟨⟨originalLength, _, horiginal⟩, hreads⟩ := hrep
  have hbound : ∀ index, largest = some index → index.val < Std.Usize.max := by
    intro index hindex
    rw [hindex] at hextent
    simp only [Option.elim_some] at hextent
    scalar_tac
  obtain ⟨length, hlength, hvalue⟩ := ProgressiveList.len_total_spec ValueInst mapInst
    { self with updates } largest hmax hbound
  refine ⟨⟨length, hlength, hvalue.trans hextent⟩, ?_⟩
  intro query
  simpa only [ProgressiveList.get, hget query,
    ProgressiveList.backing_get, ProgressiveList.backing_len] using hreads query

/-- Under read agreement, the new maximum's mathematical extent is necessary
as well as sufficient for preserving the source sequence. Exact maximum-index
identity is unnecessary, and the represented length implies its successor fits. -/
theorem ProgressiveList.represents_with_updates_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (updates : U)
    (hget : ∀ query, mapInst.get updates query = mapInst.get self.updates query) :
    ({ self with updates } : ProgressiveList T U).Represents ValueInst mapInst contents ↔
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length := by
  constructor
  · rintro ⟨⟨length, hlength, hvalue⟩, _⟩
    cases hmax : mapInst.max_index updates with
    | fail error | div => simp [ProgressiveList.len, utils.updated_length, hmax] at hlength
    | ok largest =>
      refine ⟨largest, rfl, ?_⟩
      have hbound := (ProgressiveList.len_success_iff ValueInst mapInst
        { self with updates } largest hmax).mp ⟨length, hlength⟩
      obtain ⟨computed, hcomputed, hextent⟩ := ProgressiveList.len_total_spec ValueInst mapInst
        { self with updates } largest hmax hbound
      have heq : computed = length := ok.inj (hcomputed.symm.trans hlength)
      simpa only [heq, hvalue] using hextent.symm
  · rintro ⟨largest, hmax, hextent⟩
    exact ProgressiveList.Represents.with_updates_of_max_index ValueInst mapInst
      self contents hrep updates largest hmax hget hextent

end milhouse.progressive_list
