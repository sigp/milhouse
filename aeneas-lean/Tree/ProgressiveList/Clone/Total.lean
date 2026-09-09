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

/-- The actual public clone terminates, preserves the complete represented
sequence and backing validity, and returns precisely the cloned pending map.
Only that map call must terminate and preserve its reads and logical extent;
its maximum may change below the backing length. No element clone, packing,
or map/maximum identity law is required, and no successful list-clone or
new list-length call is assumed. -/
theorem ProgressiveList.clone_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hmap : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates ∧
      (∀ query, mapInst.get updates query = mapInst.get self.updates query) ∧
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length) :
    ∃ result, ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.tree = self.tree ∧ result.length = self.length ∧
      mapInst.corecloneCloneInst.clone self.updates = ok result.updates := by
  obtain ⟨updates, hclone, hget, hmax⟩ := hmap
  have hcall : ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok { self with updates } := by
    rw [ProgressiveList.clone_eq, hclone]
    rfl
  refine ⟨{ self with updates }, hcall, ?_, hbacking, rfl, rfl, hclone⟩
  apply ProgressiveList.clone_represents ValueInst mapInst self contents hrep _ _ hcall
  · intro output houtput
    have heq : output = updates := ok.inj (houtput.symm.trans hclone)
    simpa only [heq] using hget
  · intro output houtput
    have heq : output = updates := ok.inj (houtput.symm.trans hclone)
    simpa only [heq] using hmax

end milhouse.progressive_list
