import Tree.ProgressiveList.Clone

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Cloning the list succeeds exactly when cloning its pending map succeeds.
No element operation, packing law, or representation invariant is involved. -/
theorem ProgressiveList.clone_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U) :
    (∃ result, ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result) ↔
    ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates := by
  constructor
  · rintro ⟨result, hclone⟩
    obtain ⟨updates, hmap, _⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hclone
    exact ⟨updates, hmap⟩
  · rintro ⟨updates, hmap⟩
    refine ⟨{ self with updates }, ?_⟩
    rw [ProgressiveList.clone_eq, hmap]
    rfl

/-- Successful sequence-preserving cloning is equivalent to termination of
the actual pending-map clone with precisely the lookup/extent outcomes needed
by the represented sequence. Raw map-read and maximum identity are unnecessary. -/
theorem ProgressiveList.clone_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) :
    (∃ result, ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result ∧
      result.Represents ValueInst mapInst contents) ↔
    ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates ∧
      self.UpdateReadsAgree ValueInst mapInst updates ∧
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length := by
  constructor
  · rintro ⟨result, hclone, hresult⟩
    obtain ⟨updates, hmap, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hclone
    exact ⟨updates, hmap,
      (ProgressiveList.represents_with_updates_iff ValueInst mapInst self contents hrep updates).mp hresult⟩
  · rintro ⟨updates, hmap, hreads, hmax⟩
    refine ⟨{ self with updates }, ?_, ?_⟩
    · rw [ProgressiveList.clone_eq, hmap]
      rfl
    · exact (ProgressiveList.represents_with_updates_iff
        ValueInst mapInst self contents hrep updates).mpr ⟨hreads, hmax⟩

/-- The actual public clone terminates, preserves the complete represented
sequence and backing validity, and returns precisely the cloned pending map.
Only that map call must terminate and preserve reads after the backing fallback
and logical extent; its maximum may change below the backing length. No element
clone, packing, or map/maximum identity law is required, and no successful list-clone or
new list-length call is assumed. -/
theorem ProgressiveList.clone_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hmap : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates ∧
      self.UpdateReadsAgree ValueInst mapInst updates ∧
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length) :
    ∃ result, ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.tree = self.tree ∧ result.length = self.length ∧
      mapInst.corecloneCloneInst.clone self.updates = ok result.updates := by
  obtain ⟨result, hcall, hresult⟩ :=
    (ProgressiveList.clone_success_represents_iff ValueInst mapInst self contents hrep).mpr hmap
  obtain ⟨updates, hclone, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcall
  exact ⟨{ self with updates }, hcall, hresult, hbacking, rfl, rfl, hclone⟩

end milhouse.progressive_list
