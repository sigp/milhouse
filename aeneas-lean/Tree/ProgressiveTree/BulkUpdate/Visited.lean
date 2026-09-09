import Tree.ProgressiveTree.BulkUpdate.CloneScope
import Tree.ProgressiveTree.BulkUpdate.Steps
import Tree.ProgressiveTree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem step_of_geometry {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {before after : ProgressiveTree T}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    ProgressiveTree.BulkStep ValueInst mapInst updates maximum next start stop binary before after := by
  obtain ⟨actualStart, actualNext, actualStop, actualBinary, hstart, hnext, hstop, hbinary, hstep⟩ :=
    ProgressiveTree.with_updated_leaves_recursive_step ValueInst mapInst hupdate
  rw [hgeometry.start_eq] at hstart
  cases hstart
  rw [hgeometry.next_eq] at hnext
  cases hnext
  rw [hgeometry.stop_eq] at hstop
  cases hstop
  rw [hgeometry.binary_eq] at hbinary
  cases hbinary
  exact hstep

/-- Successful progressive rebuilding supplies an actual successful binary
update at every selected input layer, without map, metadata, clone, or input
invariant laws. -/
theorem ProgressiveTree.BulkLayerVisited.update_success {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {before after : ProgressiveTree T}
    {depth : Std.U32} {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    ∃ result, tree.Tree.with_updated_leaves ValueInst mapInst layer updates 0#usize start binary none =
      ok (.Ok result) := by
  induction hvisit generalizing after with
  | zero_here hgeometry hhas =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ hleft _ => exact ⟨_, hleft⟩
  | node_here hgeometry hhas =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ hleft _ =>
      rcases hleft with ⟨hempty, _⟩ | ⟨_, hleft⟩
      · rw [hhas] at hempty; cases hempty
      · exact ⟨_, hleft⟩
  | zero_tail hgeometry hhas hselected _ ih =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive
  | node_tail hgeometry _ hselected _ ih =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive

/-- A selected input layer inherits binary shape from the progressive input.
The actual depth conversion supplies its index; neither rebuilding success nor
a packing or range correctness law is assumed. -/
theorem ProgressiveTree.BulkLayerVisited.shape {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum factor : Option Std.Usize} {before : ProgressiveTree T}
    {depth : Std.U32} {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hshape : before.Shape factor depth.val) : layer.Shape factor binary.val := by
  induction hvisit with
  | zero_here _ _ => exact .zero factor _
  | node_here hgeometry _ =>
    cases hshape with
    | node _ hleft _ =>
      have hbinary := ProgressiveTree.binary_depth_successor_val ValueInst
        hgeometry.next_eq hgeometry.binary_eq
      simpa only [hbinary] using hleft
  | zero_tail _ _ _ _ ih => exact ih (.zero factor _)
  | @node_tail hash left right depth next start stop binary layer layerStart layerDepth has
      hgeometry _ _ _ ih =>
    cases hshape with
    | node _ _ hright =>
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hgeometry.next_eq] at hadd
      simp at hadd
      have hnext : next.val = depth.val + 1 := by omega
      exact ih (by simpa only [hnext] using hright)

end milhouse.progressive_tree
