import Tree.ProgressiveTree.Rebase.Pointer
import Tree.ProgressiveList.Rebase.State

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_list

/-- Rebasing onto a shared backing tree succeeds and leaves the complete list
unchanged. No representation, packing, comparison, cache, or map law is needed. -/
theorem ProgressiveList.rebase_on_of_tree_ptr_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    (hpointer : triomphe.arc.Arc.ptr_eq self.tree base.tree = ok true) :
    ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), self) := by
  obtain ⟨same, hsame, htrees⟩ := triomphe.arc.Arc.ptr_eq_spec self.tree base.tree
  have htrue : same = true := by simpa [hpointer] using hsame.symm
  have hequal := htrees htrue
  rw [ProgressiveList.rebase_on_eq,
    progressive_tree.ProgressiveTree.rebase_on_of_ptr_eq ValueInst self.tree base.tree
      self.length base.length hpointer]
  simp [← hequal]

/-- With shared backing, nonmutating rebasing performs exactly the pending-map
clone. This equation includes clone failure and divergence, and assumes no
clone termination, identity, or preservation law. -/
theorem ProgressiveList.rebase_of_tree_ptr_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self base : ProgressiveList T U)
    (hpointer : triomphe.arc.Arc.ptr_eq self.tree base.tree = ok true) :
    ProgressiveList.rebase ValueInst mapInst self base = (do
      let updates ← mapInst.corecloneCloneInst.clone self.updates
      ok (.Ok { self with updates })) := by
  rw [ProgressiveList.rebase, ProgressiveList.clone_eq]
  cases mapInst.corecloneCloneInst.clone self.updates with
  | fail error => rfl
  | div => rfl
  | ok updates =>
    simp only [bind_tc_ok]
    rw [ProgressiveList.rebase_on_of_tree_ptr_eq ValueInst mapInst { self with updates } base hpointer]
    rfl

end milhouse.progressive_list
