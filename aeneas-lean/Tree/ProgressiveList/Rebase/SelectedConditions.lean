import Tree.ProgressiveTree.Rebase.SelectedSuccess
import Tree.ProgressiveList.Rebase.State

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- At a fixed packing layout, the selected arithmetic, binary geometry, and
element-call conditions exactly characterize public in-place success. No
whole-tree shape, representable-layer, density, accurate-length, semantic
comparison/hash, pending-map, or assumed subcall-success premise is required. -/
theorem ProgressiveList.rebase_on_success_iff_requirements {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) :
    (∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) ↔
      self.tree.RebaseRequirements ValueInst.corecmpPartialEqInst base.tree factor
        packingDepth.val self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase⟩
    obtain ⟨newTree, htree, _⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
    exact (progressive_tree.ProgressiveTree.rebase_on_success_iff_requirements ValueInst hlayout
      self.tree base.tree self.length base.length).mp ⟨newTree, htree⟩
  · intro hinputs
    obtain ⟨newTree, htree⟩ := (progressive_tree.ProgressiveTree.rebase_on_success_iff_requirements ValueInst hlayout
      self.tree base.tree self.length base.length).mpr hinputs
    refine ⟨{ self with tree := newTree }, ?_⟩
    rw [ProgressiveList.rebase_on_eq, htree]
    rfl

/-- Public nonmutating success requires exactly the selected backing-tree
conditions and termination of the actual pending-map clone. The clone needs
no identity or observer-preservation law, and saturated metadata is retained.
Only the fixed packing layout is assumed outside this exact criterion. -/
theorem ProgressiveList.rebase_success_iff_requirements {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) :
    (∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) ↔
      (∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates) ∧
      self.tree.RebaseRequirements ValueInst.corecmpPartialEqInst base.tree factor
        packingDepth.val self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase⟩
    obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
    obtain ⟨updates, hupdates, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
    exact ⟨⟨updates, hupdates⟩, (ProgressiveList.rebase_on_success_iff_requirements ValueInst mapInst hlayout
      { self with updates } base).mp ⟨result, hrebased⟩⟩
  · rintro ⟨⟨updates, hclone⟩, hinputs⟩
    obtain ⟨result, hrebase⟩ := (ProgressiveList.rebase_on_success_iff_requirements ValueInst mapInst hlayout
      { self with updates } base).mpr hinputs
    refine ⟨result, ?_⟩
    simp! only [ProgressiveList.rebase, ProgressiveList.clone_eq, hclone, bind_tc_ok,
      hrebase, core.result.Result.Insts.CoreOpsTry.branch]

end milhouse.progressive_list
