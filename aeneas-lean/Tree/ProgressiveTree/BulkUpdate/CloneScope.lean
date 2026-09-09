import Tree.BulkUpdate.CloneScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- The checked geometry used before selecting a progressive update layer.
These are the actual scalar/capacity queries, not an assumed update result. -/
structure ProgressiveTree.BulkLayerGeometry {T : Type} (ValueInst : Value T)
    (depth next : Std.U32) (start stop binary : Std.Usize) : Prop where
  start_eq : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start
  next_eq : depth + 1#u32 = ok next
  stop_eq : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop
  binary_eq : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary

/-- A binary layer selected by the progressive traversal's range and maximum
queries. An empty zero layer stops the traversal; an existing node can skip
its left layer and still visit the suffix. No bulk-update call or result is
part of this relation. -/
inductive ProgressiveTree.BulkLayerVisited {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) : ProgressiveTree T → Std.U32 → tree.Tree T → Std.Usize → Std.Usize → Prop
  | zero_here {depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
      BulkLayerVisited ValueInst mapInst updates maximum .ProgressiveZero depth (.Zero binary) start binary
  | node_here {hash left right depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
      BulkLayerVisited ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth left start binary
  | zero_tail {depth next start stop binary layer layerStart layerDepth}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hvisit : BulkLayerVisited ValueInst mapInst updates maximum .ProgressiveZero next layer layerStart layerDepth) :
      BulkLayerVisited ValueInst mapInst updates maximum .ProgressiveZero depth layer layerStart layerDepth
  | node_tail {hash left right depth next start stop binary layer layerStart layerDepth has}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hvisit : BulkLayerVisited ValueInst mapInst updates maximum right next layer layerStart layerDepth) :
      BulkLayerVisited ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth layer layerStart layerDepth

/-- A clone-input law only on selected progressive layers and, within each
layer, the inputs selected by the binary update. This scopes value preservation
or clone termination without requiring either for arbitrary element values. -/
def ProgressiveTree.BulkCloneOn {T U : Type} (P : T → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    layer.BulkCloneOn P mapInst updates factor binary.val start.val

theorem ProgressiveTree.BulkCloneOn.of_all {T U : Type} {P : T → Prop}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize) (hP : ∀ value, P value)
    (self : ProgressiveTree T) (depth : Std.U32) :
    self.BulkCloneOn P ValueInst mapInst updates factor maximum depth := by
  intro layer start binary _
  exact tree.Tree.BulkCloneOn.of_all mapInst updates factor hP layer binary.val start.val

theorem ProgressiveTree.BulkCloneOn.mono {T U : Type} {P Q : T → Prop}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (hPQ : ∀ value, P value → Q value) (self : ProgressiveTree T) (depth : Std.U32)
    (hself : self.BulkCloneOn P ValueInst mapInst updates factor maximum depth) :
    self.BulkCloneOn Q ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact tree.Tree.BulkCloneOn.mono mapInst updates factor hPQ layer binary.val start.val
    (hself layer start binary hvisit)

theorem ProgressiveTree.BulkCloneOn.zero_left {T U : Type} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneOn
      P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    (tree.Tree.Zero binary : tree.Tree T).BulkCloneOn P mapInst updates factor binary.val start.val :=
  hself _ _ _ (.zero_here hgeometry hhas)

theorem ProgressiveTree.BulkCloneOn.node_left {T U : Type} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkCloneOn
      P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    left.BulkCloneOn P mapInst updates factor binary.val start.val :=
  hself _ _ _ (.node_here hgeometry hhas)

theorem ProgressiveTree.BulkCloneOn.zero_right {T U : Type} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneOn
      P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneOn
      P ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  exact hself _ _ _ (.zero_tail hgeometry hhas hmaximum hvisit)

theorem ProgressiveTree.BulkCloneOn.node_right {T U : Type} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkCloneOn
      P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkCloneOn P ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_tail hgeometry hhas hmaximum hvisit)

end milhouse.progressive_tree
