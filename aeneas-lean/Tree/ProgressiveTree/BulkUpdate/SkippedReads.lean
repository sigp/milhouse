import Tree.ProgressiveTree.BulkUpdate.Skipped
import Tree.ProgressiveTree.BulkUpdate.Steps

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

/-- A successful update preserves the complete read result of every skipped
suffix. The maximum guards themselves route the query through all ancestors;
no packing, shape, clone, range-correctness, or lookup-termination law is needed. -/
theorem ProgressiveTree.BulkSuffixSkipped.get_after_eq_suffix {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {before after suffix : ProgressiveTree T}
    {depth suffixDepth : Std.U32} {start query : Std.Usize}
    (hskip : before.BulkSuffixSkipped ValueInst mapInst updates maximum depth suffix suffixDepth start)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hquery : start.val ≤ query.val) :
    ProgressiveTree.get_recursive ValueInst after query depth =
      ProgressiveTree.get_recursive ValueInst suffix query suffixDepth := by
  induction hskip generalizing after with
  | zero_here hgeometry hhas hbefore =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand hash _ _ hright =>
      rcases hright with ⟨_, rfl⟩ | ⟨⟨last, hlast, hbound⟩, _⟩
      · exact node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq hquery
      · have := hbefore last hlast
        omega
  | node_here hgeometry _ hbefore =>
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨_, rfl⟩ | ⟨⟨last, hlast, hbound⟩, _⟩
      · exact node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq hquery
      · have := hbefore last hlast
        omega
  | @zero_tail depth next start stop binary suffix suffixDepth suffixStart hgeometry hhas hselected hskip ih =>
    have hroute : stop.val ≤ query.val := by
      obtain ⟨last, hlast, hbound⟩ := hselected
      have := hskip.maximum_before last hlast
      exact Nat.le_trans hbound (by omega)
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand hash _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · rw [node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq hroute]
        exact ih hrecursive hquery
  | @node_tail hash left right depth next start stop binary has suffix suffixDepth suffixStart
      hgeometry _ hselected hskip ih =>
    have hroute : stop.val ≤ query.val := by
      obtain ⟨last, hlast, hbound⟩ := hselected
      have := hskip.maximum_before last hlast
      exact Nat.le_trans hbound (by omega)
    have hstep := step_of_geometry hgeometry hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · rw [node_get_right ValueInst hgeometry.next_eq hgeometry.stop_eq hroute]
        exact ih hrecursive hquery

/-- Correct materialization of pending reads forces agreement on every
skipped suffix. This necessity direction requires no clone or map semantics,
and makes no assumptions about absent pending values. -/
theorem ProgressiveTree.with_updated_leaves_recursive_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T}
    {depth : Std.U32} {newLength : Nat}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hreads : ∀ query value, query.val < newLength → mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst after query depth = ok (some value)) :
    before.BulkSkippedValuesAgree ValueInst mapInst updates maximum newLength depth := by
  intro suffix suffixDepth start hskip query value hlo hhi hget
  rw [← hskip.get_after_eq_suffix hupdate hlo]
  exact hreads query value hhi hget

/-- The public update obtains the maximum internally; successful pending-read
materialization therefore implies skipped-value agreement for its actual answer. -/
theorem ProgressiveTree.with_updated_leaves_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {before after : ProgressiveTree T} {newLength : Nat}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after))
    (hreads : ∀ query value, query.val < newLength → mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst after query 0#u32 = ok (some value)) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkSkippedValuesAgree ValueInst mapInst updates maximum newLength 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_skipped_values_agree ValueInst mapInst updates hupdate hreads

end milhouse.progressive_tree
