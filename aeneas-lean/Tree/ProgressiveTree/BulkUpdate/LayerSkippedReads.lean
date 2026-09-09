import Tree.ProgressiveTree.BulkUpdate.LayerSkipped
import Tree.ProgressiveTree.BulkUpdate.Steps
import Tree.ProgressiveTree.CapacitySuccess

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

private theorem node_get_right {T : Type} (ValueInst : Value T)
    {left : tree.Tree T} {right : ProgressiveTree T}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {depth next : Std.U32} {stop query : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hquery : stop.val ≤ query.val) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode hash left right) query depth =
      ProgressiveTree.get_recursive ValueInst right query next := by
  have hroute : ¬ query < stop := by scalar_tac
  rw [ProgressiveTree.get_recursive]
  simp only [hnext, hstop, bind_tc_ok, if_neg hroute, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]

private theorem node_get_same_left {T : Type} (ValueInst : Value T)
    {left : tree.Tree T} {oldRight newRight : ProgressiveTree T}
    {oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {depth next : Std.U32} {stop query : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hroute : query < stop) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode newHash left newRight) query depth =
      ProgressiveTree.get_recursive ValueInst (.ProgressiveNode oldHash left oldRight) query depth := by
  rw [ProgressiveTree.get_recursive, ProgressiveTree.get_recursive]
  simp only [hnext, hstop, bind_tc_ok, if_pos hroute]

/-- Every reached skipped layer starts at or after the original layer.
Actual successful capacity calculations suffice, including saturation. -/
theorem ProgressiveTree.BulkLayerSkipped.start_after {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {self layer : ProgressiveTree T}
    {depth layerDepth : Std.U32} {start stop capacity : Std.Usize}
    (hskip : self.BulkLayerSkipped ValueInst mapInst updates maximum depth layer layerDepth start stop)
    (hcapacity : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok capacity) :
    capacity.val ≤ start.val := by
  induction hskip generalizing capacity with
  | zero_here hgeometry _ =>
    rw [hgeometry.start_eq] at hcapacity
    cases hcapacity
    exact Nat.le_refl _
  | node_here hgeometry _ =>
    rw [hgeometry.start_eq] at hcapacity
    cases hcapacity
    exact Nat.le_refl _
  | @zero_tail depth next _ _ _ _ _ _ _ hgeometry _ _ _ ih =>
    have hadd := UScalar.add_equiv depth 1#u32
    rw [hgeometry.next_eq] at hadd
    simp at hadd
    exact Nat.le_trans
      (ProgressiveTree.total_capacity_success_mono ValueInst hcapacity hgeometry.stop_eq (by omega))
      (ih hgeometry.stop_eq)
  | @node_tail _ _ _ depth next _ _ _ _ _ _ _ _ hgeometry _ _ _ ih =>
    have hadd := UScalar.add_equiv depth 1#u32
    rw [hgeometry.next_eq] at hadd
    simp at hadd
    exact Nat.le_trans
      (ProgressiveTree.total_capacity_success_mono ValueInst hcapacity hgeometry.stop_eq (by omega))
      (ih hgeometry.stop_eq)

/-- The original tree routes each query in a skipped layer to its recorded
input subtree. Only actual input geometry and guard observations are used. -/
theorem ProgressiveTree.BulkLayerSkipped.get_before_eq_layer {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {before layer : ProgressiveTree T}
    {depth layerDepth : Std.U32} {start stop query : Std.Usize}
    (hskip : before.BulkLayerSkipped ValueInst mapInst updates maximum depth layer layerDepth start stop)
    (hlo : start.val ≤ query.val) :
    ProgressiveTree.get_recursive ValueInst before query depth =
      ProgressiveTree.get_recursive ValueInst layer query layerDepth := by
  induction hskip with
  | zero_here _ _ => rfl
  | node_here _ _ => rfl
  | zero_tail _ _ _ _ ih => simpa only [ProgressiveTree.get_recursive] using ih hlo
  | @node_tail hash left right depth next start stop binary has layer layerDepth layerStart layerStop
      hgeometry _ _ hskip ih =>
    rw [node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq
      (Nat.le_trans (hskip.start_after hgeometry.stop_eq) hlo)]
    exact ih hlo

/-- A successful update preserves the entire read result in a skipped
progressive layer. Ancestor routing follows from the actual capacities;
no packing, shape, clone, range-correctness, or lookup-termination law is needed. -/
theorem ProgressiveTree.BulkLayerSkipped.get_after_eq_layer {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {before after layer : ProgressiveTree T}
    {depth layerDepth : Std.U32} {start stop query : Std.Usize}
    (hskip : before.BulkLayerSkipped ValueInst mapInst updates maximum depth layer layerDepth start stop)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hlo : start.val ≤ query.val) (hhi : query.val < stop.val) :
    ProgressiveTree.get_recursive ValueInst after query depth =
      ProgressiveTree.get_recursive ValueInst layer query layerDepth := by
  induction hskip generalizing after with
  | zero_here hgeometry hhas =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero _ => rfl
    | expand _ htrue _ _ => rw [hhas] at htrue; cases htrue
  | node_here hgeometry hhas =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ hleft _ =>
      rcases hleft with ⟨_, rfl⟩ | ⟨htrue, _⟩
      · exact node_get_same_left ValueInst hgeometry.next_eq hgeometry.stop_eq (by scalar_tac)
      · rw [hhas] at htrue
        cases htrue
  | @zero_tail depth next start stop binary layer layerDepth layerStart layerStop
      hgeometry hhas hselected hskip ih =>
    have hroute : stop.val ≤ query.val := Nat.le_trans (hskip.start_after hgeometry.stop_eq) hlo
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · rw [node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq hroute]
        exact ih hrecursive hlo hhi
  | @node_tail hash left right depth next start stop binary has layer layerDepth layerStart layerStop
      hgeometry _ hselected hskip ih =>
    have hroute : stop.val ≤ query.val := Nat.le_trans (hskip.start_after hgeometry.stop_eq) hlo
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · rw [node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq hroute]
        exact ih hrecursive hlo hhi

/-- Correct materialized reads for present pending values require agreement
with unchanged input reads in every skipped progressive layer. -/
theorem ProgressiveTree.with_updated_leaves_recursive_layer_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T}
    {depth : Std.U32} {newLength : Nat}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hreads : ∀ query value, query.val < newLength → mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst after query depth = ok (some value)) :
    before.BulkLayerSkippedValuesAgree ValueInst mapInst updates maximum newLength depth := by
  intro layer layerDepth start stop hskip query value hlo hstop hhi hget
  rw [← hskip.get_after_eq_layer hupdate hlo hstop]
  exact hreads query value hhi hget

/-- Public successful updates imply skipped-layer agreement for their actual
maximum answer whenever the output materializes every present pending read. -/
theorem ProgressiveTree.with_updated_leaves_layer_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {before after : ProgressiveTree T} {newLength : Nat}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after))
    (hreads : ∀ query value, query.val < newLength → mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst after query 0#u32 = ok (some value)) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkLayerSkippedValuesAgree ValueInst mapInst updates maximum newLength 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_layer_skipped_values_agree
    ValueInst mapInst updates hupdate hreads

end milhouse.progressive_tree
