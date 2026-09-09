import Tree.ProgressiveTree.BulkUpdate.LayerRangeScope
import Tree.ProgressiveTree.BulkUpdate.Range

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- An input progressive layer skipped by an actual false range answer.
The recorded subtree supplies the unchanged reads in its layer interval.
Later layers follow the actual range and maximum guards; no update call or
result occurs in this relation. -/
inductive ProgressiveTree.BulkLayerSkipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) :
    ProgressiveTree T → Std.U32 → ProgressiveTree T → Std.U32 → Std.Usize → Std.Usize → Prop
  | zero_here {depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
      BulkLayerSkipped ValueInst mapInst updates maximum .ProgressiveZero depth .ProgressiveZero depth start stop
  | node_here {hash left right depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
      BulkLayerSkipped ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth (.ProgressiveNode hash left right) depth start stop
  | zero_tail {depth next start stop binary suffix suffixDepth suffixStart suffixStop}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hskip : BulkLayerSkipped ValueInst mapInst updates maximum .ProgressiveZero next suffix suffixDepth suffixStart suffixStop) :
      BulkLayerSkipped ValueInst mapInst updates maximum .ProgressiveZero depth suffix suffixDepth suffixStart suffixStop
  | node_tail {hash left right depth next start stop binary has suffix suffixDepth suffixStart suffixStop}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hskip : BulkLayerSkipped ValueInst mapInst updates maximum right next suffix suffixDepth suffixStart suffixStop) :
      BulkLayerSkipped ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth suffix suffixDepth suffixStart suffixStop

theorem ProgressiveTree.BulkLayerSkipped.false_range {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {self layer : ProgressiveTree T}
    {depth layerDepth : Std.U32} {start stop : Std.Usize}
    (hskip : self.BulkLayerSkipped ValueInst mapInst updates maximum depth layer layerDepth start stop) :
    ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false := by
  induction hskip with
  | zero_here _ hhas => exact hhas
  | node_here _ hhas => exact hhas
  | zero_tail _ _ _ _ ih => exact ih
  | node_tail _ _ _ _ ih => exact ih

theorem ProgressiveTree.BulkLayerSkipped.range_queried {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {self layer : ProgressiveTree T}
    {depth layerDepth : Std.U32} {start stop : Std.Usize}
    (hskip : self.BulkLayerSkipped ValueInst mapInst updates maximum depth layer layerDepth start stop)
    (hnonempty : start.val < stop.val) :
    self.BulkLayerRangeQueried ValueInst mapInst updates maximum depth start stop := by
  induction hskip with
  | zero_here hgeometry _ => exact .here hgeometry hnonempty
  | node_here hgeometry _ => exact .here hgeometry hnonempty
  | zero_tail hgeometry hhas hmaximum _ ih => exact .zero_tail hgeometry hhas hmaximum (ih hnonempty)
  | node_tail hgeometry hhas hmaximum _ ih => exact .node_tail hgeometry hhas hmaximum (ih hnonempty)

/-- Present pending values in a skipped progressive layer agree with its
unchanged input reads. Only values inside both the layer interval and the
new logical prefix matter. Missing entries impose no lookup law. -/
def ProgressiveTree.BulkLayerSkippedValuesAgree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (newLength : Nat)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer layerDepth start stop,
    self.BulkLayerSkipped ValueInst mapInst updates maximum depth layer layerDepth start stop →
    ∀ query value, start.val ≤ query.val → query.val < stop.val → query.val < newLength →
      mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst layer query layerDepth = ok (some value)

/-- False range exclusion implies agreement by ruling out every present
pending value, but agreement also permits redundant matching entries. -/
theorem ProgressiveTree.BulkLayerSkippedValuesAgree.of_ranges {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (newLength : Nat)
    (hrange : self.BulkLayerRangeOn (update_map.RangeExcludesValuesAt mapInst updates)
      ValueInst mapInst updates maximum depth) :
    self.BulkLayerSkippedValuesAgree ValueInst mapInst updates maximum newLength depth := by
  intro layer layerDepth start stop hskip query value hlo hhi _ hget
  have hnone := ProgressiveTree.has_updates_in_range_false_excludes ValueInst mapInst
    (fun hnonempty => hrange _ _ (hskip.range_queried hnonempty)) hskip.false_range hget hlo hhi
  cases hnone

theorem ProgressiveTree.BulkLayerSkippedValuesAgree.zero_here {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
    ∀ query value, start.val ≤ query.val → query.val < stop.val → query.val < newLength →
      mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst .ProgressiveZero query depth = ok (some value) :=
  hself _ _ _ _ (.zero_here hgeometry hhas)

theorem ProgressiveTree.BulkLayerSkippedValuesAgree.node_here {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
    ∀ query value, start.val ≤ query.val → query.val < stop.val → query.val < newLength →
      mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst (.ProgressiveNode hash left right) query depth = ok (some value) :=
  hself _ _ _ _ (.node_here hgeometry hhas)

theorem ProgressiveTree.BulkLayerSkippedValuesAgree.zero_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerSkippedValuesAgree
      ValueInst mapInst updates maximum newLength next := by
  intro suffix suffixDepth suffixStart suffixStop hskip
  exact hself _ _ _ _ (.zero_tail hgeometry hhas hmaximum hskip)

theorem ProgressiveTree.BulkLayerSkippedValuesAgree.node_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkLayerSkippedValuesAgree ValueInst mapInst updates maximum newLength next := by
  intro suffix suffixDepth suffixStart suffixStop hskip
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ _ (.node_tail hgeometry hhas hmaximum hskip)

end milhouse.progressive_tree
