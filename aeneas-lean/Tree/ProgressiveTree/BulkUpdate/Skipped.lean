import Tree.ProgressiveTree.BulkUpdate.CloneScope
import Tree.UpdateMap.Domain

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- An input suffix skipped by the progressive maximum guard. Reached layers
are selected using the actual geometry and range answers, without assuming
any bulk-update call or result. An empty zero layer exits before this guard. -/
inductive ProgressiveTree.BulkSuffixSkipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) :
    ProgressiveTree T → Std.U32 → ProgressiveTree T → Std.U32 → Std.Usize → Prop
  | zero_here {depth next start stop binary}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hbefore : ∀ last, maximum = some last → last.val < stop.val) :
      BulkSuffixSkipped ValueInst mapInst updates maximum .ProgressiveZero depth .ProgressiveZero next stop
  | node_here {hash left right depth next start stop binary has}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
      (hbefore : ∀ last, maximum = some last → last.val < stop.val) :
      BulkSuffixSkipped ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth right next stop
  | zero_tail {depth next start stop binary suffix suffixDepth suffixStart}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hskip : BulkSuffixSkipped ValueInst mapInst updates maximum .ProgressiveZero next suffix suffixDepth suffixStart) :
      BulkSuffixSkipped ValueInst mapInst updates maximum .ProgressiveZero depth suffix suffixDepth suffixStart
  | node_tail {hash left right depth next start stop binary has suffix suffixDepth suffixStart}
      (hgeometry : BulkLayerGeometry ValueInst depth next start stop binary)
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
      (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val)
      (hskip : BulkSuffixSkipped ValueInst mapInst updates maximum right next suffix suffixDepth suffixStart) :
      BulkSuffixSkipped ValueInst mapInst updates maximum (.ProgressiveNode hash left right) depth suffix suffixDepth suffixStart

theorem ProgressiveTree.BulkSuffixSkipped.maximum_before {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {self suffix : ProgressiveTree T}
    {depth suffixDepth : Std.U32} {start : Std.Usize}
    (hskip : self.BulkSuffixSkipped ValueInst mapInst updates maximum depth suffix suffixDepth start) :
    ∀ last, maximum = some last → last.val < start.val := by
  induction hskip with
  | zero_here _ _ hbefore => exact hbefore
  | node_here _ _ hbefore => exact hbefore
  | zero_tail _ _ _ _ ih => exact ih
  | node_tail _ _ _ _ ih => exact ih

/-- Pending values in a selected skipped suffix already agree with its
unchanged backing reads. Only indices inside the new logical prefix matter;
absent pending values impose no read or termination law. -/
def ProgressiveTree.BulkSkippedValuesAgree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (newLength : Nat)
    (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ suffix suffixDepth start,
    self.BulkSuffixSkipped ValueInst mapInst updates maximum depth suffix suffixDepth start →
    ∀ query value, start.val ≤ query.val → query.val < newLength →
      mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst suffix query suffixDepth = ok (some value)

/-- The old maximum law rules out every such pending value. It is sufficient
but need not hold for redundant matching entries in unchanged backing. -/
theorem ProgressiveTree.BulkSkippedValuesAgree.of_maximum {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} (newLength : Nat)
    (hmaximum : update_map.MaximumBoundsValues mapInst updates maximum)
    (self : ProgressiveTree T) (depth : Std.U32) :
    self.BulkSkippedValuesAgree ValueInst mapInst updates maximum newLength depth := by
  intro suffix suffixDepth start hskip query value hlo _ hget
  have hnone := update_map.get_none_of_maximum_before mapInst updates hmaximum
    hskip.maximum_before hlo hget
  cases hnone

theorem ProgressiveTree.BulkSkippedValuesAgree.zero_here {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hbefore : ∀ last, maximum = some last → last.val < stop.val) :
    ∀ query value, stop.val ≤ query.val → query.val < newLength →
      mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst .ProgressiveZero query next = ok (some value) :=
  hself _ _ _ (.zero_here hgeometry hhas hbefore)

theorem ProgressiveTree.BulkSkippedValuesAgree.node_here {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hbefore : ∀ last, maximum = some last → last.val < stop.val) :
    ∀ query value, stop.val ≤ query.val → query.val < newLength →
      mapInst.get updates query = ok (some value) →
      ProgressiveTree.get_recursive ValueInst right query next = ok (some value) := by
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_here hgeometry hhas hbefore)

theorem ProgressiveTree.BulkSkippedValuesAgree.zero_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkSkippedValuesAgree
      ValueInst mapInst updates maximum newLength next := by
  intro suffix suffixDepth suffixStart hskip
  exact hself _ _ _ (.zero_tail hgeometry hhas hmaximum hskip)

theorem ProgressiveTree.BulkSkippedValuesAgree.node_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {maximum : Option Std.Usize} {newLength : Nat}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkSkippedValuesAgree
      ValueInst mapInst updates maximum newLength depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkSkippedValuesAgree ValueInst mapInst updates maximum newLength next := by
  intro suffix suffixDepth suffixStart hskip
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_tail hgeometry hhas hmaximum hskip)

end milhouse.progressive_tree
