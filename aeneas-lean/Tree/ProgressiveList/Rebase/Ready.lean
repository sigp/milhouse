import Tree.ProgressiveTree.Rebase.Ready
import Tree.ProgressiveList.Rebase.State

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Public in-place success is equivalent to the complete selected-input
criterion. Packing queries are required only for entered node pairs. No
layout/coherence, global query success, shape, capacity, density, accurate
length, semantic comparison/hash, or pending-map premise is assumed. -/
theorem ProgressiveList.rebase_on_success_iff_ready {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) :
    (∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) ↔
      self.tree.RebaseReady ValueInst base.tree self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase⟩
    obtain ⟨newTree, htree, _⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
    exact (progressive_tree.ProgressiveTree.rebase_on_success_iff_ready ValueInst
      self.tree base.tree self.length base.length).mp ⟨newTree, htree⟩
  · intro hready
    obtain ⟨newTree, htree⟩ := (progressive_tree.ProgressiveTree.rebase_on_success_iff_ready ValueInst
      self.tree base.tree self.length base.length).mpr hready
    refine ⟨{ self with tree := newTree }, ?_⟩
    rw [ProgressiveList.rebase_on_eq, htree]
    rfl

/-- Nonmutating success is equivalent to termination of the actual pending-map
clone and the complete backing-input criterion. The clone remains necessary
on immediate tree shortcuts; packing queries do not. No global packing law,
clone identity, or observer-preservation law is required. -/
theorem ProgressiveList.rebase_success_iff_ready {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U) :
    (∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) ↔
      (∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates) ∧
      self.tree.RebaseReady ValueInst base.tree self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase⟩
    obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
    obtain ⟨updates, hupdates, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
    exact ⟨⟨updates, hupdates⟩, (ProgressiveList.rebase_on_success_iff_ready ValueInst mapInst
      { self with updates } base).mp ⟨result, hrebased⟩⟩
  · rintro ⟨⟨updates, hclone⟩, hready⟩
    obtain ⟨result, hrebase⟩ := (ProgressiveList.rebase_on_success_iff_ready ValueInst mapInst
      { self with updates } base).mpr hready
    refine ⟨result, ?_⟩
    simp! only [ProgressiveList.rebase, ProgressiveList.clone_eq, hclone, bind_tc_ok,
      hrebase, core.result.Result.Insts.CoreOpsTry.branch]

end milhouse.progressive_list
