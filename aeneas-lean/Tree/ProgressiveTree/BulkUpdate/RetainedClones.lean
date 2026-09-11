import Tree.BulkUpdate.RetainedClones
import Tree.ProgressiveTree.BulkUpdate.SelectedSlots

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Pending values override the old mathematical slots throughout a suffix,
including holes beyond its stored contents. Only actual successful map reads
are constrained; no lookup-termination law is part of this relation. -/
def ProgressiveTree.BulkSlotContents {T U : Type}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (before after : ProgressiveTree T) (depth : Nat) : Prop :=
  ∀ (query : Std.Usize) (pending : Option T), mapInst.get updates query = ok pending →
    progressiveCapacity factor depth ≤ query.val →
    after.slot factor depth (query.val - progressiveCapacity factor depth) =
      pending.or (before.slot factor depth (query.val - progressiveCapacity factor depth))


/-- Correct progressive slots restrict to correct contents of each selected
binary result. Actual selected execution supplies that result; no input shape,
density, clone, range, or termination law is needed. -/
theorem ProgressiveTree.BulkLayerVisited.update_success_contents {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T} {depth : Std.U32}
    {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hcontents : ProgressiveTree.BulkSlotContents mapInst updates factor before after depth.val) :
    ∃ result, tree.Tree.with_updated_leaves ValueInst mapInst layer updates 0#usize start binary none =
      ok (.Ok result) ∧
      tree.Tree.BulkContents mapInst updates factor layer result binary.val 0 start.val := by
  obtain ⟨result, hresult, hslots⟩ := hvisit.update_success_slots hlayout hupdate
  obtain ⟨layerDepth, hdepth, hstart, _⟩ := hvisit.position hlayout
  have hrootLo := progressiveCapacity_mono factor hdepth
  rw [← hstart] at hrootLo
  refine ⟨result, hresult, ?_⟩
  intro query pending hget hlo hhi
  simp only [Nat.zero_add] at hlo hhi
  have hread := hcontents query pending hget (Nat.le_trans hrootLo hlo)
  rw [hslots query.val hlo hhi, hvisit.slot_before_eq_layer hlayout hlo hhi] at hread
  exact hread

/-- Correct mathematical slots after successful progressive rebuilding force
identity of every selected pending clone and retained stored clone. Layout and
input shape suffice; range, density, capacity, clone, and termination laws are
not assumed. -/
theorem ProgressiveTree.with_updated_leaves_recursive_retained_clone_identity {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hshape : before.Shape factor depth.val)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hcontents : ProgressiveTree.BulkSlotContents mapInst updates factor before after depth.val) :
    before.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
      ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  obtain ⟨result, hresult, hbinaryContents⟩ := hvisit.update_success_contents hlayout hupdate hcontents
  obtain ⟨layerDepth, hdepth, hstart, _⟩ := hvisit.position hlayout
  have halign : start.val % tree.leafCapacity factor = 0 := by
    rw [hstart]
    exact progressiveCapacity_aligned factor layerDepth
  simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
    tree.Tree.with_updated_leaves_retained_clone_identity ValueInst mapInst hlayout
      (hvisit.shape hshape) (by simp) halign hresult hbinaryContents

/-- The public progressive wrapper supplies the retained/pending identity
condition for its actual maximum answer whenever its final slots are correct. -/
theorem ProgressiveTree.with_updated_leaves_retained_clone_identity {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T}
    (hshape : before.Shape factor 0)
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after))
    (hcontents : ProgressiveTree.BulkSlotContents mapInst updates factor before after 0) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_retained_clone_identity
    ValueInst mapInst updates hlayout hshape hupdate hcontents

end milhouse.progressive_tree
