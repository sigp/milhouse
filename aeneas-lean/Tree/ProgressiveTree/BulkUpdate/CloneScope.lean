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

/-- Separate storage and pending laws on precisely the binary layers selected
by the progressive traversal. Each selected binary tree further restricts the
laws to its selected children. -/
def ProgressiveTree.BulkCloneScope {T U : Type}
    (stored : packed_leaf.PackedLeaf T → Nat → Prop) (pending : T → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    layer.BulkCloneScope stored pending mapInst updates factor binary.val start.val

/-- A value law on every selected clone input, including overwritten storage. -/
abbrev ProgressiveTree.BulkCloneOn {T U : Type} (P : T → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  self.BulkCloneScope (fun leaf _ => ∀ value ∈ leaf.values.val, P value)
    P ValueInst mapInst updates factor maximum depth

/-- Content laws concern only retained stored slots and selected pending values. -/
abbrev ProgressiveTree.BulkRetainedCloneOn {T U : Type} (P : T → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  self.BulkCloneScope (tree.PackedRetainedCloneOn P mapInst updates (tree.leafCapacity factor))
    P ValueInst mapInst updates factor maximum depth

/-- Total clone laws require stored termination and surviving-value identity
only on selected progressive layers and binary children. -/
def ProgressiveTree.BulkCloneLaws {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    layer.BulkCloneLaws ValueInst.corecloneCloneInst mapInst updates factor binary.val start.val

theorem ProgressiveTree.BulkCloneLaws.terminates {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hself : self.BulkCloneLaws ValueInst mapInst updates factor maximum depth) :
    self.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact (hself layer start binary hvisit).terminates

theorem ProgressiveTree.BulkCloneLaws.preserves {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hself : self.BulkCloneLaws ValueInst mapInst updates factor maximum depth) :
    self.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
      ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact (hself layer start binary hvisit).preserves

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


/-- Existing all-input laws imply the retained-slot law. -/
theorem ProgressiveTree.BulkCloneOn.retained {T U : Type} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hself : self.BulkCloneOn P ValueInst mapInst updates factor maximum depth) :
    self.BulkRetainedCloneOn P ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact tree.Tree.BulkCloneOn.retained (hself layer start binary hvisit)

/-- Stronger all-input identity laws specialize to the total clone laws. -/
theorem ProgressiveTree.BulkCloneOn.to_laws {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hself : self.BulkCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
      ValueInst mapInst updates factor maximum depth) :
    self.BulkCloneLaws ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact tree.Tree.BulkCloneOn.to_laws (hself layer start binary hvisit)

theorem ProgressiveTree.BulkCloneScope.zero_left {T U : Type} {S : packed_leaf.PackedLeaf T → Nat → Prop} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneScope
      S P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    (tree.Tree.Zero binary : tree.Tree T).BulkCloneScope S P mapInst updates factor binary.val start.val :=
  hself _ _ _ (.zero_here hgeometry hhas)

theorem ProgressiveTree.BulkCloneScope.node_left {T U : Type} {S : packed_leaf.PackedLeaf T → Nat → Prop} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkCloneScope
      S P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    left.BulkCloneScope S P mapInst updates factor binary.val start.val :=
  hself _ _ _ (.node_here hgeometry hhas)

theorem ProgressiveTree.BulkCloneScope.zero_right {T U : Type} {S : packed_leaf.PackedLeaf T → Nat → Prop} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneScope
      S P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneScope
      S P ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  exact hself _ _ _ (.zero_tail hgeometry hhas hmaximum hvisit)

theorem ProgressiveTree.BulkCloneScope.node_right {T U : Type} {S : packed_leaf.PackedLeaf T → Nat → Prop} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkCloneScope
      S P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkCloneScope S P ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_tail hgeometry hhas hmaximum hvisit)

theorem ProgressiveTree.BulkCloneOn.zero_left {T U : Type} {P : T → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkCloneOn
      P ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    (tree.Tree.Zero binary : tree.Tree T).BulkCloneOn P mapInst updates factor binary.val start.val :=
  ProgressiveTree.BulkCloneScope.zero_left hself hgeometry hhas

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
  ProgressiveTree.BulkCloneScope.node_left hself hgeometry hhas

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
