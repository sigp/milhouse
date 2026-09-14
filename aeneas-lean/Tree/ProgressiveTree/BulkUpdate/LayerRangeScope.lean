import Tree.ProgressiveTree.BulkUpdate.RangeScope
import Tree.UpdateMap.RangeExtent

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Range queries at reached progressive layers. Binary child queries are
handled separately; recursive layers follow the actual range/maximum guards. -/
inductive ProgressiveTree.BulkLayerRangeQueried {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) : ProgressiveTree T → Std.U32 → Std.Usize → Std.Usize → Prop
  | here {before depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hnonempty : start.val < stop.val) :
      BulkLayerRangeQueried ValueInst mapInst updates maximum before depth start stop
  | zero_tail {depth next start stop binary lo hi}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hquery : BulkLayerRangeQueried ValueInst mapInst updates maximum .ProgressiveZero next lo hi) :
      BulkLayerRangeQueried ValueInst mapInst updates maximum .ProgressiveZero depth lo hi
  | node_tail {hash left right depth next start stop binary has lo hi}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hquery : BulkLayerRangeQueried ValueInst mapInst updates maximum right next lo hi) :
      BulkLayerRangeQueried ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth lo hi

theorem ProgressiveTree.BulkLayerRangeQueried.to_range {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum factor : Option Std.Usize} {self : ProgressiveTree T}
    {depth : Std.U32} {lo hi : Std.Usize}
    (h : self.BulkLayerRangeQueried ValueInst mapInst updates maximum depth lo hi) :
    self.BulkRangeQueried ValueInst mapInst updates factor maximum depth lo hi := by
  induction h with
  | here hgeometry hnonempty => exact .here hgeometry hnonempty
  | zero_tail hgeometry hhas hmaximum _ ih => exact .zero_tail hgeometry hhas hmaximum ih
  | node_tail hgeometry hhas hmaximum _ ih => exact .node_tail hgeometry hhas hmaximum ih

/-- A range law restricted to progressive layer queries. -/
def ProgressiveTree.BulkLayerRangeOn {T U : Type} (Q : Std.Usize → Std.Usize → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ lo hi, self.BulkLayerRangeQueried ValueInst mapInst updates maximum depth lo hi → Q lo hi

theorem ProgressiveTree.BulkRangeOn.layers {T U : Type} {P Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hself : self.BulkRangeOn P ValueInst mapInst updates factor maximum depth)
    (hPQ : ∀ lo hi, P lo hi → Q lo hi) :
    self.BulkLayerRangeOn Q ValueInst mapInst updates maximum depth := by
  intro lo hi hquery
  exact hPQ lo hi (hself lo hi hquery.to_range)

theorem ProgressiveTree.BulkLayerRangeOn.here {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {self : ProgressiveTree T}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : self.BulkLayerRangeOn Q ValueInst mapInst updates maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hnonempty : start.val < stop.val) : Q start stop :=
  hself _ _ (.here hgeometry hnonempty)

theorem ProgressiveTree.BulkLayerRangeOn.zero_right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerRangeOn
      Q ValueInst mapInst updates maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerRangeOn
      Q ValueInst mapInst updates maximum next := by
  intro lo hi hquery
  exact hself _ _ (.zero_tail hgeometry hhas hmaximum hquery)

theorem ProgressiveTree.BulkLayerRangeOn.node_right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerRangeOn
      Q ValueInst mapInst updates maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkLayerRangeOn Q ValueInst mapInst updates maximum next := by
  intro lo hi hquery
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ (.node_tail hgeometry hhas hmaximum hquery)

/-- A range law on binary queries within the selected progressive layers. -/
def ProgressiveTree.BulkBinaryRangeOn {T U : Type} (Q : Std.Usize → Std.Usize → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    tree.BulkRangeOn Q mapInst updates factor binary.val start.val

theorem ProgressiveTree.BulkLayerVisited.range_queried {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    {layer : tree.Tree T} {start binary lo hi : Std.Usize}
    (hvisit : self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hquery : tree.BulkRangeQueried mapInst updates factor binary.val start.val lo hi) :
    self.BulkRangeQueried ValueInst mapInst updates factor maximum depth lo hi := by
  induction hvisit with
  | zero_here hgeometry hhas => exact .binary hgeometry hhas hquery
  | node_here hgeometry hhas => exact .binary hgeometry hhas hquery
  | zero_tail hgeometry hhas hmaximum _ ih => exact .zero_tail hgeometry hhas hmaximum (ih hquery)
  | node_tail hgeometry hhas hmaximum _ ih => exact .node_tail hgeometry hhas hmaximum (ih hquery)

theorem ProgressiveTree.BulkRangeOn.binary_layers {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hself : self.BulkRangeOn Q ValueInst mapInst updates factor maximum depth) :
    self.BulkBinaryRangeOn Q ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit lo hi hquery
  exact hself lo hi (hvisit.range_queried hquery)

theorem ProgressiveTree.BulkBinaryRangeOn.zero_left {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkBinaryRangeOn
      Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkRangeOn Q mapInst updates factor binary.val start.val :=
  hself _ _ _ (.zero_here hgeometry hhas)

theorem ProgressiveTree.BulkBinaryRangeOn.node_left {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkBinaryRangeOn
      Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkRangeOn Q mapInst updates factor binary.val start.val :=
  hself _ _ _ (.node_here hgeometry hhas)

theorem ProgressiveTree.BulkBinaryRangeOn.zero_right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkBinaryRangeOn
      Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkBinaryRangeOn
      Q ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  exact hself _ _ _ (.zero_tail hgeometry hhas hmaximum hvisit)

theorem ProgressiveTree.BulkBinaryRangeOn.node_right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkBinaryRangeOn
      Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkBinaryRangeOn Q ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_tail hgeometry hhas hmaximum hvisit)

/-- Every scoped range query belongs either to a progressive layer or to a
selected binary layer. This classification uses only input traversal guards. -/
theorem ProgressiveTree.BulkRangeQueried.layer_or_binary {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    {lo hi : Std.Usize}
    (hquery : self.BulkRangeQueried ValueInst mapInst updates factor maximum depth lo hi) :
    self.BulkLayerRangeQueried ValueInst mapInst updates maximum depth lo hi ∨
      ∃ layer start binary,
        self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary ∧
        tree.BulkRangeQueried mapInst updates factor binary.val start.val lo hi := by
  induction hquery with
  | here hgeometry hnonempty => exact Or.inl (.here hgeometry hnonempty)
  | @binary before depth next start stop binary lo hi hgeometry hhas hquery =>
    cases before with
    | ProgressiveZero => exact Or.inr ⟨_, _, _, .zero_here hgeometry hhas, hquery⟩
    | ProgressiveNode hash left right => exact Or.inr ⟨_, _, _, .node_here hgeometry hhas, hquery⟩
  | zero_tail hgeometry hhas hmaximum _ ih =>
    rcases ih with hquery | ⟨layer, start, binary, hvisit, hquery⟩
    · exact Or.inl (.zero_tail hgeometry hhas hmaximum hquery)
    · exact Or.inr ⟨layer, start, binary, .zero_tail hgeometry hhas hmaximum hvisit, hquery⟩
  | node_tail hgeometry hhas hmaximum _ ih =>
    rcases ih with hquery | ⟨layer, start, binary, hvisit, hquery⟩
    · exact Or.inl (.node_tail hgeometry hhas hmaximum hquery)
    · exact Or.inr ⟨layer, start, binary, .node_tail hgeometry hhas hmaximum hvisit, hquery⟩

/-- The complete query scope is exactly the union of progressive queries and
queries inside selected binary layers, with no successful update assumed. -/
theorem ProgressiveTree.BulkRangeOn.iff_layers_binary {T U : Type}
    (Q : Std.Usize → Std.Usize → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor maximum : Option Std.Usize) (self : ProgressiveTree T) (depth : Std.U32) :
    self.BulkRangeOn Q ValueInst mapInst updates factor maximum depth ↔
      self.BulkLayerRangeOn Q ValueInst mapInst updates maximum depth ∧
      self.BulkBinaryRangeOn Q ValueInst mapInst updates factor maximum depth := by
  constructor
  · intro hqueries
    exact ⟨hqueries.layers (fun _ _ h => h), hqueries.binary_layers⟩
  · rintro ⟨hlayers, hbinary⟩ lo hi hquery
    rcases hquery.layer_or_binary with hquery | ⟨layer, start, binary, hvisit, hquery⟩
    · exact hlayers lo hi hquery
    · exact hbinary layer start binary hvisit lo hi hquery

end milhouse.progressive_tree
