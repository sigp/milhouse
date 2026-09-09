import Tree.BulkUpdate.Activation
import Tree.ProgressiveTree.BulkUpdate.LayerRangeScope
import Tree.ProgressiveTree.BulkUpdate.Range

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Clamping progressive endpoints can only shorten their binary layer
window. This bound holds even when either endpoint saturates. -/
theorem ProgressiveTree.BulkLayerGeometry.window_le_capacity {T : Type}
    {ValueInst : Value T} {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary) :
    stop.val - start.val ≤ tree.subtreeCapacity factor binary.val := by
  have hadd := UScalar.add_equiv depth 1#u32
  rw [hgeometry.next_eq] at hadd
  simp at hadd
  have hnextVal : next.val = depth.val + 1 := by omega
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hgeometry.next_eq hgeometry.binary_eq
  obtain ⟨actualStart, hactualStart, hstartVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
  obtain ⟨actualStop, hactualStop, hstopVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq next
  rw [hgeometry.start_eq] at hactualStart
  cases hactualStart
  rw [hgeometry.stop_eq] at hactualStop
  cases hactualStop
  rw [hnextVal, progressiveCapacity_succ, ← hbinaryVal] at hstopVal
  omega

/-- Every selected binary layer can start rebuilding: it contains a pending
value or is a packed terminal. No condition is imposed on a layer skipped by
a false progressive answer. This scope mentions no rebuilding result. -/
def ProgressiveTree.BulkLayerEnabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    tree.BulkUpdateEnabled mapInst updates factor binary.val start.val

/-- The previous full range law supplies a pending value in every selected
layer. It is stronger than the start condition, especially for packed terminals. -/
theorem ProgressiveTree.BulkLayerEnabled.of_ranges {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hrange : self.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth) :
    self.BulkLayerEnabled ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  induction hvisit with
  | @zero_here depth next start stop binary hgeometry hhas =>
    obtain ⟨hnonempty, hmap⟩ := ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas
    obtain ⟨index, hlo, hhi, hvalue⟩ := ((hrange.here hgeometry hnonempty) true hmap).mp rfl
    have hwidth := hgeometry.window_le_capacity hlayout
    refine Or.inr ⟨index - start.val, by omega, ?_⟩
    have heq : start.val + (index - start.val) = index := by omega
    rwa [heq]
  | @node_here hash left right depth next start stop binary hgeometry hhas =>
    obtain ⟨hnonempty, hmap⟩ := ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas
    obtain ⟨index, hlo, hhi, hvalue⟩ := ((hrange.here hgeometry hnonempty) true hmap).mp rfl
    have hwidth := hgeometry.window_le_capacity hlayout
    refine Or.inr ⟨index - start.val, by omega, ?_⟩
    have heq : start.val + (index - start.val) = index := by omega
    rwa [heq]
  | zero_tail hgeometry hhas hmaximum _ ih =>
    exact ih (hrange.zero_right hgeometry hhas hmaximum)
  | node_tail hgeometry hhas hmaximum _ ih =>
    exact ih (hrange.node_right hgeometry ⟨_, hhas⟩ hmaximum)

theorem ProgressiveTree.BulkLayerEnabled.zero_left {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerEnabled
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkUpdateEnabled mapInst updates factor binary.val start.val :=
  hself _ _ _ (.zero_here hgeometry hhas)

theorem ProgressiveTree.BulkLayerEnabled.node_left {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerEnabled
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkUpdateEnabled mapInst updates factor binary.val start.val :=
  hself _ _ _ (.node_here hgeometry hhas)

theorem ProgressiveTree.BulkLayerEnabled.zero_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerEnabled
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerEnabled
      ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  exact hself _ _ _ (.zero_tail hgeometry hhas hmaximum hvisit)

theorem ProgressiveTree.BulkLayerEnabled.node_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerEnabled
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkLayerEnabled ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_tail hgeometry hhas hmaximum hvisit)

end milhouse.progressive_tree
