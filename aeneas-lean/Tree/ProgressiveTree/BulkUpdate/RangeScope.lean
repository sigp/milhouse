import Tree.BulkUpdate.RangeScope
import Tree.ProgressiveTree.BulkUpdate.CloneScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- A range queried by progressive bulk traversal. Each reached nonempty
layer window is queried before selecting its binary update. Binary queries
and later layers follow the same range/maximum guards as the Rust traversal.
Only input geometry and external observations occur in this relation. -/
inductive ProgressiveTree.BulkRangeQueried {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize) :
    ProgressiveTree T → Std.U32 → Std.Usize → Std.Usize → Prop
  | here {before depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hnonempty : start.val < stop.val) :
      BulkRangeQueried ValueInst mapInst updates factor maximum before depth start stop
  | binary {before depth next start stop binary lo hi}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hquery : tree.BulkRangeQueried mapInst updates factor binary.val start.val lo hi) :
      BulkRangeQueried ValueInst mapInst updates factor maximum before depth lo hi
  | zero_tail {depth next start stop binary lo hi}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hquery : BulkRangeQueried ValueInst mapInst updates factor maximum .ProgressiveZero next lo hi) :
      BulkRangeQueried ValueInst mapInst updates factor maximum .ProgressiveZero depth lo hi
  | node_tail {hash left right depth next start stop binary has lo hi}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hquery : BulkRangeQueried ValueInst mapInst updates factor maximum right next lo hi) :
      BulkRangeQueried ValueInst mapInst updates factor maximum (.ProgressiveNode hash left right) depth lo hi

/-- An external range law restricted to reached progressive layers and the
binary queries selected within them. -/
def ProgressiveTree.BulkRangeOn {T U : Type} (Q : Std.Usize → Std.Usize → Prop)
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (maximum : Option Std.Usize)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ lo hi, self.BulkRangeQueried ValueInst mapInst updates factor maximum depth lo hi → Q lo hi

theorem ProgressiveTree.BulkRangeOn.of_all {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor maximum : Option Std.Usize) (hQ : ∀ lo hi, Q lo hi)
    (self : ProgressiveTree T) (depth : Std.U32) :
    self.BulkRangeOn Q ValueInst mapInst updates factor maximum depth := by
  intro lo hi _
  exact hQ lo hi

theorem ProgressiveTree.BulkRangeOn.mono {T U : Type} {P Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hPQ : ∀ lo hi, P lo hi → Q lo hi)
    (hself : self.BulkRangeOn P ValueInst mapInst updates factor maximum depth) :
    self.BulkRangeOn Q ValueInst mapInst updates factor maximum depth := by
  intro lo hi hquery
  exact hPQ lo hi (hself lo hi hquery)

theorem ProgressiveTree.BulkRangeOn.here {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : self.BulkRangeOn Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hnonempty : start.val < stop.val) : Q start stop :=
  hself _ _ (.here hgeometry hnonempty)

theorem ProgressiveTree.BulkRangeOn.binary {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : self.BulkRangeOn Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkRangeOn Q mapInst updates factor binary.val start.val := by
  intro lo hi hquery
  exact hself _ _ (.binary hgeometry hhas hquery)

theorem ProgressiveTree.BulkRangeOn.zero_right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkRangeOn
      Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkRangeOn
      Q ValueInst mapInst updates factor maximum next := by
  intro lo hi hquery
  exact hself _ _ (.zero_tail hgeometry hhas hmaximum hquery)

theorem ProgressiveTree.BulkRangeOn.node_right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkRangeOn
      Q ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkRangeOn Q ValueInst mapInst updates factor maximum next := by
  intro lo hi hquery
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ (.node_tail hgeometry hhas hmaximum hquery)

end milhouse.progressive_tree
