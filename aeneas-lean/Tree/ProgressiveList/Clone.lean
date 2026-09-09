import Tree.ProgressiveList.Clone.Maximum

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Cloning shares the backing tree and copies its recorded length; only the
    pending map invokes its generic clone implementation. -/
theorem ProgressiveList.clone_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U) :
    ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = (do
        let updates ← mapInst.corecloneCloneInst.clone self.updates
        ok { self with updates }) := by
  simp [ProgressiveList.Insts.CoreCloneClone.clone, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
    utils.Length.Insts.CoreCloneClone.clone]

theorem ProgressiveList.clone_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U)
    {result : ProgressiveList T U}
    (hclone : ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result) :
    ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates ∧
      result = { self with updates } := by
  rw [ProgressiveList.clone_eq] at hclone
  cases hmap : mapInst.corecloneCloneInst.clone self.updates with
  | fail e => simp [hmap] at hclone
  | div => simp [hmap] at hclone
  | ok updates =>
    simp only [hmap, bind_tc_ok, ok.injEq] at hclone
    exact ⟨updates, rfl, hclone.symm⟩

/-- Successful cloning preserves backing validity without any element or
    map clone law, since the materialized backing state is unchanged. -/
theorem ProgressiveList.clone_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U)
    {factor : Option Std.Usize} (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (hclone : ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result) :
    result.BackingValid factor := by
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hclone
  exact hbacking

/-- Cloning preserves the represented sequence when cloning the pending map
    preserves its reads and logical extent. Its maximum may change below the
    backing length. No element-clone law or exact map/maximum identity is needed. -/
theorem ProgressiveList.clone_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∀ query, mapInst.get updates query = mapInst.get self.updates query)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length)
    {result : ProgressiveList T U}
    (hclone : ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result) :
    result.Represents ValueInst mapInst contents := by
  obtain ⟨updates, hupdates, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hclone
  obtain ⟨largest, hmax, hextent⟩ := hmapMax updates hupdates
  exact ProgressiveList.Represents.with_updates_of_max_index ValueInst mapInst
    self contents hrep updates largest hmax (hmapGet updates hupdates) hextent

/-- The pending-update observer is preserved under the corresponding map
    clone law, independently of sequence or backing invariants. -/
theorem ProgressiveList.has_pending_updates_after_clone {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (self : ProgressiveList T U)
    (hmapEmpty : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      mapInst.is_empty updates = mapInst.is_empty self.updates)
    {result : ProgressiveList T U}
    (hclone : ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result) :
    ProgressiveList.has_pending_updates ValueInst mapInst result =
      ProgressiveList.has_pending_updates ValueInst mapInst self := by
  obtain ⟨updates, hupdates, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hclone
  simp only [ProgressiveList.has_pending_updates, hmapEmpty updates hupdates]

end milhouse.progressive_list
