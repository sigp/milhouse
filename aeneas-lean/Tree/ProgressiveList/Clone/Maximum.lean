import Tree.ProgressiveList.Backing
import Tree.ProgressiveList.Lookup

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Replacing the pending map preserves the represented sequence when its
reads agree after the actual backing fallback and its maximum gives the same
logical length. Raw reads and maxima may differ. Represented contents supply
every successor bound; no successful list-length call is assumed for the new map. -/
theorem ProgressiveList.Represents.with_updates_of_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (updates : U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index updates = ok largest)
    (hget : self.UpdateReadsAgree ValueInst mapInst updates)
    (hextent : largest.elim self.length.val
      (fun index => max (index.val + 1) self.length.val) = contents.length) :
    ({ self with updates } : ProgressiveList T U).Represents ValueInst mapInst contents := by
  obtain ⟨⟨originalLength, _, horiginal⟩, hreads⟩ := hrep
  refine ⟨⟨originalLength, ?_, horiginal⟩, ?_⟩
  · rw [ProgressiveList.len_eq_updated_length]
    exact (utils.updated_length_eq_ok_iff mapInst self.length updates originalLength).mpr
      ⟨largest, hmax, hextent.trans horiginal.symm⟩
  · intro query
    exact ((ProgressiveList.get_with_updates_eq_iff ValueInst mapInst self updates query).mpr
      (hget query)).trans (hreads query)

/-- Under read agreement after the backing fallback, the new maximum's extent
is necessary as well as sufficient for preserving the source sequence. Exact
maximum-index identity is unnecessary, and representation implies its successor fits. -/
theorem ProgressiveList.represents_with_updates_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (updates : U)
    (hget : self.UpdateReadsAgree ValueInst mapInst updates) :
    ({ self with updates } : ProgressiveList T U).Represents ValueInst mapInst contents ↔
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length := by
  constructor
  · rintro ⟨⟨length, hlength, hvalue⟩, _⟩
    rw [ProgressiveList.len_eq_updated_length] at hlength
    obtain ⟨largest, hmax, hextent⟩ :=
      (utils.updated_length_eq_ok_iff mapInst self.length updates length).mp hlength
    exact ⟨largest, hmax, hextent.trans hvalue⟩
  · rintro ⟨largest, hmax, hextent⟩
    exact ProgressiveList.Represents.with_updates_of_max_index ValueInst mapInst
      self contents hrep updates largest hmax hget hextent

/-- Full sequence preservation after replacing the pending map is equivalent
to raw lookup agreement at the actual fallback and matching maximum extent.
Both conditions are necessary; no separate map-read law is assumed. -/
theorem ProgressiveList.represents_with_updates_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (updates : U) :
    ({ self with updates } : ProgressiveList T U).Represents ValueInst mapInst contents ↔
      self.UpdateReadsAgree ValueInst mapInst updates ∧
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length := by
  constructor
  · intro hnew
    have hget : self.UpdateReadsAgree ValueInst mapInst updates :=
      (ProgressiveList.reads_with_updates_eq_iff ValueInst mapInst self updates).mp
        (fun query => (hnew.2 query).trans (hrep.2 query).symm)
    exact ⟨hget, (ProgressiveList.represents_with_updates_iff_max_index
      ValueInst mapInst self contents hrep updates hget).mp hnew⟩
  · rintro ⟨hget, hmax⟩
    exact (ProgressiveList.represents_with_updates_iff_max_index
      ValueInst mapInst self contents hrep updates hget).mpr hmax

end milhouse.progressive_list
