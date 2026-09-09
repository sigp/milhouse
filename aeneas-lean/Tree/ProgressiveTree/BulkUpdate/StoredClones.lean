import Tree.BulkUpdate.StoredClones
import Tree.ProgressiveTree.BulkUpdate.Visited

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- A value law on copied storage in precisely the selected progressive and
binary layers; pending values impose no condition. -/
abbrev ProgressiveTree.BulkStoredCloneOn {T U : Type} (P : T → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  self.BulkCloneScope (fun leaf _ => ∀ value ∈ leaf.values.val, P value)
    (fun _ => True) ValueInst mapInst updates factor maximum depth

/-- Total clone laws split exactly into copied-storage termination and
identity of retained slots and selected pending values. -/
theorem ProgressiveTree.BulkCloneLaws.iff_stored_and_retained {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) :
    self.BulkCloneLaws ValueInst mapInst updates factor maximum depth ↔
      self.BulkStoredCloneOn (fun value => ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
        ValueInst mapInst updates factor maximum depth ∧
      self.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst updates factor maximum depth := by
  unfold ProgressiveTree.BulkCloneLaws
  simp only [tree.Tree.BulkCloneLaws.iff_stored_and_retained, forall_and]
  rfl

/-- Actual progressive success certifies termination of every selected stored
clone. No input invariant, map law, or clone assumption is required. -/
theorem ProgressiveTree.with_updated_leaves_recursive_stored_clones_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    before.BulkStoredCloneOn (fun value => ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
      ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  obtain ⟨result, hresult⟩ := hvisit.update_success hupdate
  simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
    tree.Tree.with_updated_leaves_stored_clones_terminate ValueInst mapInst hlayout (by simp) hresult

/-- Successful public rebuilding supplies the stored clone termination law
for its actual maximum answer, including overwritten copied values. -/
theorem ProgressiveTree.with_updated_leaves_stored_clones_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after)) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkStoredCloneOn (fun value => ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
        ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_stored_clones_terminate
    ValueInst mapInst updates hlayout hupdate

end milhouse.progressive_tree
