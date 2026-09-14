import Tree.ProgressiveTree.BulkUpdate.Visited
import Tree.ProgressiveTree.BulkUpdate.Range
import Tree.ProgressiveTree.Density

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem next_val {depth next : Std.U32} (hnext : depth + 1#u32 = ok next) :
    next.val = depth.val + 1 := by
  have hadd := UScalar.add_equiv depth 1#u32
  rw [hnext] at hadd
  simp at hadd
  omega

/-- A selected layer has an unclamped mathematical start and the expected
binary depth. Its progressive depth is at least the traversal's initial depth.
Actual selection and layout suffice; no update or input invariant is needed. -/
theorem ProgressiveTree.BulkLayerVisited.position {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before : ProgressiveTree T} {depth : Std.U32}
    {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary) :
    ∃ layerDepth, depth.val ≤ layerDepth ∧ start.val = progressiveCapacity factor layerDepth ∧
      binary.val = 2 * layerDepth := by
  induction hvisit with
  | zero_here hgeometry hhas | node_here hgeometry hhas =>
    have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
    exact ⟨_, Nat.le_refl _, ProgressiveTree.total_capacity_unclamped ValueInst
      hlayout.opt_packing_factor_eq hgeometry.start_eq (by scalar_tac),
      ProgressiveTree.binary_depth_successor_val ValueInst hgeometry.next_eq hgeometry.binary_eq⟩
  | zero_tail hgeometry _ _ _ ih | node_tail hgeometry _ _ _ ih =>
    obtain ⟨layerDepth, hdepth, hstart, hbinary⟩ := ih
    have hadd := next_val hgeometry.next_eq
    exact ⟨layerDepth, by omega, hstart, hbinary⟩

private theorem node_slot_left {T : Type} (factor : Option Std.Usize)
    {left : tree.Tree T} {right : ProgressiveTree T} {depth query : Nat}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hlo : progressiveCapacity factor depth ≤ query)
    (hhi : query < progressiveCapacity factor depth + tree.subtreeCapacity factor (2 * depth)) :
    (ProgressiveTree.ProgressiveNode hash left right).slot factor depth
      (query - progressiveCapacity factor depth) =
      left.slot factor (2 * depth) (query - progressiveCapacity factor depth) := by
  have hroute : query - progressiveCapacity factor depth < tree.subtreeCapacity factor (2 * depth) := by omega
  simp only [ProgressiveTree.slot, if_pos hroute]

private theorem node_slot_right {T : Type} (factor : Option Std.Usize)
    {left : tree.Tree T} {right : ProgressiveTree T} {depth next query : Nat}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    (hnext : next = depth + 1) (hlo : progressiveCapacity factor next ≤ query) :
    (ProgressiveTree.ProgressiveNode hash left right).slot factor depth
      (query - progressiveCapacity factor depth) =
      right.slot factor next (query - progressiveCapacity factor next) := by
  subst next
  rw [progressiveCapacity_succ] at hlo ⊢
  have hroute : ¬ query - progressiveCapacity factor depth < tree.subtreeCapacity factor (2 * depth) := by omega
  simp only [ProgressiveTree.slot, if_neg hroute]
  congr 1
  omega

/-- Mathematical slots in a selected window route to its recorded input
binary layer. This includes holes and imposes no density or machine-capacity
bound on either the input tree or the query. -/
theorem ProgressiveTree.BulkLayerVisited.slot_before_eq_layer {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before : ProgressiveTree T} {depth : Std.U32}
    {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    {query : Nat} (hlo : start.val ≤ query)
    (hhi : query < start.val + tree.subtreeCapacity factor binary.val) :
    before.slot factor depth.val (query - progressiveCapacity factor depth.val) =
      layer.slot factor binary.val (query - start.val) := by
  induction hvisit with
  | zero_here _ _ => rfl
  | node_here hgeometry hhas =>
    have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
    have hstart := ProgressiveTree.total_capacity_unclamped ValueInst
      hlayout.opt_packing_factor_eq hgeometry.start_eq (by scalar_tac)
    have hbinary := ProgressiveTree.binary_depth_successor_val ValueInst hgeometry.next_eq hgeometry.binary_eq
    simpa only [hstart, hbinary] using node_slot_left factor (by simpa only [← hstart] using hlo)
        (by simpa only [← hstart, ← hbinary] using hhi)
  | zero_tail _ _ _ _ ih => exact ih hlo hhi
  | node_tail hgeometry _ _ hvisit ih =>
    obtain ⟨layerDepth, hdepth, hstart, _⟩ := hvisit.position hlayout
    have hadd := next_val hgeometry.next_eq
    have hrootLo := progressiveCapacity_mono factor hdepth
    rw [← hstart] at hrootLo
    rw [node_slot_right factor (by omega) (Nat.le_trans hrootLo hlo)]
    exact ih hlo hhi

/-- Successful rebuilding records the actual binary result at every selected
layer, and routes final mathematical slots to that result. No clone, range,
density, shape, or termination law is assumed. -/
theorem ProgressiveTree.BulkLayerVisited.update_success_slots {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T} {depth : Std.U32}
    {layer : tree.Tree T} {start binary : Std.Usize}
    (hvisit : before.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    ∃ result, tree.Tree.with_updated_leaves ValueInst mapInst layer updates 0#usize start binary none =
      ok (.Ok result) ∧
      ∀ query : Nat, start.val ≤ query → query < start.val + tree.subtreeCapacity factor binary.val →
        after.slot factor depth.val (query - progressiveCapacity factor depth.val) =
          result.slot factor binary.val (query - start.val) := by
  induction hvisit generalizing after with
  | zero_here hgeometry hhas =>
    have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
    have hstart := ProgressiveTree.total_capacity_unclamped ValueInst
      hlayout.opt_packing_factor_eq hgeometry.start_eq (by scalar_tac)
    have hbinary := ProgressiveTree.binary_depth_successor_val ValueInst hgeometry.next_eq hgeometry.binary_eq
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ hleft _ =>
      refine ⟨_, hleft, ?_⟩
      intro query hlo hhi
      simpa only [hstart, hbinary] using node_slot_left factor (by simpa only [← hstart] using hlo)
        (by simpa only [← hstart, ← hbinary] using hhi)
  | node_here hgeometry hhas =>
    have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
    have hstart := ProgressiveTree.total_capacity_unclamped ValueInst
      hlayout.opt_packing_factor_eq hgeometry.start_eq (by scalar_tac)
    have hbinary := ProgressiveTree.binary_depth_successor_val ValueInst hgeometry.next_eq hgeometry.binary_eq
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | node _ _ hleft _ =>
      rcases hleft with ⟨hempty, _⟩ | ⟨_, hleft⟩
      · rw [hhas] at hempty; cases hempty
      · refine ⟨_, hleft, ?_⟩
        intro query hlo hhi
        simpa only [hstart, hbinary] using node_slot_left factor (by simpa only [← hstart] using hlo)
          (by simpa only [← hstart, ← hbinary] using hhi)
  | zero_tail hgeometry hhas hselected hvisit ih =>
    obtain ⟨layerDepth, hdepth, hstart, _⟩ := hvisit.position hlayout
    have hadd := next_val hgeometry.next_eq
    have hrootLo := progressiveCapacity_mono factor hdepth
    rw [← hstart] at hrootLo
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · obtain ⟨result, hresult, hslots⟩ := ih hrecursive
        refine ⟨result, hresult, ?_⟩
        intro query hlo hhi
        rw [node_slot_right factor (by omega) (Nat.le_trans hrootLo hlo)]
        exact hslots query hlo hhi
  | node_tail hgeometry _ hselected hvisit ih =>
    obtain ⟨layerDepth, hdepth, hstart, _⟩ := hvisit.position hlayout
    have hadd := next_val hgeometry.next_eq
    have hrootLo := progressiveCapacity_mono factor hdepth
    rw [← hstart] at hrootLo
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · obtain ⟨result, hresult, hslots⟩ := ih hrecursive
        refine ⟨result, hresult, ?_⟩
        intro query hlo hhi
        rw [node_slot_right factor (by omega) (Nat.le_trans hrootLo hlo)]
        exact hslots query hlo hhi

end milhouse.progressive_tree
