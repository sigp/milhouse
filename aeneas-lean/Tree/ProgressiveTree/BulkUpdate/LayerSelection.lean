import Tree.BulkUpdate.Nonempty
import Tree.ProgressiveTree.BulkUpdate.LayerRangeScope
import Tree.ProgressiveTree.BulkUpdate.Steps
import Tree.ProgressiveTree.Iter.Layer

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

/-- A dense output forces every selected progressive layer to begin inside
its final logical prefix. Actual binary rebuilding constructs a nonzero tree,
whose density then forces a positive layer length. No map, clone, input
invariant, or lookup-termination law is used in this necessity direction. -/
theorem ProgressiveTree.with_updated_leaves_recursive_layer_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {newLength : Nat}
    {before after : ProgressiveTree T} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (core.result.Result.Ok after))
    (hdense : after.Dense factor depth.val (newLength - progressiveCapacity factor depth.val)) :
    before.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
      ValueInst mapInst updates maximum depth := by
  intro start stop hquery htrue
  induction hquery generalizing after with
  | @here before depth next start stop binary hgeometry hnonempty =>
    have hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true := by
      simp only [ProgressiveTree.has_updates_in_range, if_pos ((UScalar.lt_equiv _ _).mpr hnonempty), htrue]
    obtain ⟨actualStart, hactualStart, hstartVal⟩ :=
      ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq _
    rw [hgeometry.start_eq] at hactualStart
    cases hactualStart
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ hleft _ =>
      have hpositive := tree.Tree.with_updated_leaves_dense_length_pos ValueInst mapInst hleft hdense.split_layer.1
      omega
    | node _ _ hleft _ =>
      rcases hleft with ⟨hempty, _⟩ | ⟨_, hleft⟩
      · rw [hhas] at hempty
        cases hempty
      · have hpositive := tree.Tree.with_updated_leaves_dense_length_pos ValueInst mapInst hleft hdense.split_layer.1
        omega
  | @zero_tail depth next start stop binary lo hi hgeometry hhas hselected _ ih =>
    have hadd := UScalar.add_equiv depth 1#u32
    rw [hgeometry.next_eq] at hadd
    simp at hadd
    have hnextVal : next.val = depth.val + 1 := by omega
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive (by simpa only [hnextVal] using hdense.right_remainder) htrue
  | @node_tail hash left right depth next start stop binary has lo hi hgeometry _ hselected _ ih =>
    have hadd := UScalar.add_equiv depth 1#u32
    rw [hgeometry.next_eq] at hadd
    simp at hadd
    have hnextVal : next.val = depth.val + 1 := by omega
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive (by simpa only [hnextVal] using hdense.right_remainder) htrue

/-- Public successful rebuilding with dense output supplies the positive
layer-selection condition for its actual maximum answer. -/
theorem ProgressiveTree.with_updated_leaves_layer_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {newLength : Nat} {before after : ProgressiveTree T}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates =
      ok (core.result.Result.Ok after))
    (hdense : after.Dense factor 0 newLength) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
        ValueInst mapInst updates maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_layer_selection ValueInst mapInst updates hlayout
    hupdate (by simpa [progressiveCapacity] using hdense)

end milhouse.progressive_tree
