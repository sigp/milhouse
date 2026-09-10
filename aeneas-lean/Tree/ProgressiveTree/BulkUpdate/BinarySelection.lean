import Tree.BulkUpdate.Selection
import Tree.ProgressiveTree.BulkUpdate.Visited
import Tree.ProgressiveTree.BulkUpdate.Range
import Tree.ProgressiveTree.BulkUpdate.LayerRangeScope
import Tree.ProgressiveTree.Iter.Layer

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem next_val {depth next : Std.U32} (hnext : depth + 1#u32 = ok next) :
    next.val = depth.val + 1 := by
  have hadd := UScalar.add_equiv depth 1#u32
  rw [hnext] at hadd
  simp at hadd
  omega

/-- Dense progressive output gives an actual successful result and exact
clipped dense length for each selected binary layer. Layout and execution
identify the layer; no input invariant, capacity, clone, range-value, or
termination law is assumed. -/

theorem ProgressiveTree.BulkLayerVisited.update_success_dense {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {newLength : Nat} {before after : ProgressiveTree T}
    {depth : Std.U32} {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hdense : after.Dense factor depth.val (newLength - progressiveCapacity factor depth.val)) :
    ∃ result, tree.Tree.with_updated_leaves ValueInst mapInst layer updates 0#usize start binary none =
      ok (.Ok result) ∧
      tree.DenseTree factor result binary.val
        (min (newLength - start.val) (tree.subtreeCapacity factor binary.val)) := by
  induction hvisit generalizing after with
  | zero_here hgeometry hhas =>
    have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
    have hstartVal := ProgressiveTree.total_capacity_unclamped ValueInst
      hlayout.opt_packing_factor_eq hgeometry.start_eq (by scalar_tac)
    have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst
      hgeometry.next_eq hgeometry.binary_eq
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ hleft _ => exact ⟨_, hleft, by simpa only [hstartVal, hbinaryVal] using hdense.split_layer.1⟩
  | node_here hgeometry hhas =>
    have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
    have hstartVal := ProgressiveTree.total_capacity_unclamped ValueInst
      hlayout.opt_packing_factor_eq hgeometry.start_eq (by scalar_tac)
    have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst
      hgeometry.next_eq hgeometry.binary_eq
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | node _ _ hleft _ =>
      rcases hleft with ⟨hempty, _⟩ | ⟨_, hleft⟩
      · rw [hhas] at hempty; cases hempty
      · exact ⟨_, hleft, by simpa only [hstartVal, hbinaryVal] using hdense.split_layer.1⟩
  | zero_tail hgeometry hhas hselected _ ih =>
    have hnextVal := next_val hgeometry.next_eq
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive (by simpa only [hnextVal] using hdense.right_remainder)
  | node_tail hgeometry _ hselected _ ih =>
    have hnextVal := next_val hgeometry.next_eq
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive (by simpa only [hnextVal] using hdense.right_remainder)

/-- Successful rebuilding with dense output forces numeric positive selection
inside every selected binary layer. No input invariant, range-value, clone,
capacity, or termination law is required. -/
theorem ProgressiveTree.with_updated_leaves_recursive_binary_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {newLength : Nat}
    {before after : ProgressiveTree T} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hdense : after.Dense factor depth.val (newLength - progressiveCapacity factor depth.val)) :
    before.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
      ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  obtain ⟨result, hresult, hresultDense⟩ := hvisit.update_success_dense hlayout hupdate hdense
  have hselected := tree.Tree.with_updated_leaves_range_selection_of_prefix
    ValueInst mapInst hlayout (by simp) hresult (by simpa using hresultDense)
  simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using hselected

/-- The public wrapper supplies binary selection for its actual maximum
whenever successful rebuilding produces dense backing. -/
theorem ProgressiveTree.with_updated_leaves_binary_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {newLength : Nat} {before after : ProgressiveTree T}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after))
    (hdense : after.Dense factor 0 newLength) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
        ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_binary_selection ValueInst mapInst updates hlayout
    hupdate (by simpa [progressiveCapacity] using hdense)

end milhouse.progressive_tree
