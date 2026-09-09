import Tree.Shape
import Tree.UpdateMap.Range

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- A range queried by binary bulk traversal. Both immediate child ranges
are queried; deeper ranges are queried only below a positive child answer.
The relation uses input geometry and map answers, with no update result. -/
inductive BulkRangeQueried {T U : Type} (mapInst : update_map.UpdateMap U T)
    (updates : U) (factor : Option Std.Usize) : Nat → Nat → Std.Usize → Std.Usize → Prop
  | left_here {depth start lo hi}
      (hlo : lo.val = start)
      (hhi : hi.val = start + subtreeCapacity factor depth) :
      BulkRangeQueried mapInst updates factor (depth + 1) start lo hi
  | right_here {depth start lo hi}
      (hlo : lo.val = start + subtreeCapacity factor depth)
      (hhi : hi.val = start + subtreeCapacity factor depth + subtreeCapacity factor depth) :
      BulkRangeQueried mapInst updates factor (depth + 1) start lo hi
  | left_tail {depth start lo hi queryLo queryHi}
      (hlo : lo.val = start)
      (hhi : hi.val = start + subtreeCapacity factor depth)
      (hhas : mapInst.has_any_in_range updates lo hi = ok true)
      (hquery : BulkRangeQueried mapInst updates factor depth start queryLo queryHi) :
      BulkRangeQueried mapInst updates factor (depth + 1) start queryLo queryHi
  | right_tail {depth start lo hi queryLo queryHi}
      (hlo : lo.val = start + subtreeCapacity factor depth)
      (hhi : hi.val = start + subtreeCapacity factor depth + subtreeCapacity factor depth)
      (hhas : mapInst.has_any_in_range updates lo hi = ok true)
      (hquery : BulkRangeQueried mapInst updates factor depth
        (start + subtreeCapacity factor depth) queryLo queryHi) :
      BulkRangeQueried mapInst updates factor (depth + 1) start queryLo queryHi

/-- An external range law restricted to queries selected by binary traversal. -/
def BulkRangeOn {T U : Type} (Q : Std.Usize → Std.Usize → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (depth start : Nat) : Prop :=
  ∀ lo hi, BulkRangeQueried mapInst updates factor depth start lo hi → Q lo hi

/-- Leaf updates do not perform range queries. -/
theorem BulkRangeOn.zero {T U : Type} (Q : Std.Usize → Std.Usize → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (start : Nat) : BulkRangeOn Q mapInst updates factor 0 start := by
  intro lo hi hquery
  cases hquery

theorem BulkRangeOn.of_all {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (hQ : ∀ lo hi, Q lo hi) (depth start : Nat) :
    BulkRangeOn Q mapInst updates factor depth start := by
  intro lo hi _
  exact hQ lo hi

theorem BulkRangeOn.mono {T U : Type} {P Q : Std.Usize → Std.Usize → Prop}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat} (hPQ : ∀ lo hi, P lo hi → Q lo hi)
    (hself : BulkRangeOn P mapInst updates factor depth start) :
    BulkRangeOn Q mapInst updates factor depth start := by
  intro lo hi hquery
  exact hPQ lo hi (hself lo hi hquery)

/-- Reflection supplies exclusion at the same queried ranges. -/
theorem BulkRangeOn.excludesValues {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat}
    (hself : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth start) :
    BulkRangeOn (update_map.RangeExcludesValuesAt mapInst updates)
      mapInst updates factor depth start :=
  hself.mono (fun _ _ h => h.excludesValues)

theorem BulkRangeOn.left_query {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat} {lo hi : Std.Usize}
    (hself : BulkRangeOn Q mapInst updates factor (depth + 1) start)
    (hlo : lo.val = start) (hhi : hi.val = start + subtreeCapacity factor depth) : Q lo hi :=
  hself lo hi (.left_here hlo hhi)

theorem BulkRangeOn.right_query {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat} {lo hi : Std.Usize}
    (hself : BulkRangeOn Q mapInst updates factor (depth + 1) start)
    (hlo : lo.val = start + subtreeCapacity factor depth)
    (hhi : hi.val = start + subtreeCapacity factor depth + subtreeCapacity factor depth) : Q lo hi :=
  hself lo hi (.right_here hlo hhi)

theorem BulkRangeOn.left {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat} {lo hi : Std.Usize}
    (hself : BulkRangeOn Q mapInst updates factor (depth + 1) start)
    (hlo : lo.val = start) (hhi : hi.val = start + subtreeCapacity factor depth)
    (hhas : mapInst.has_any_in_range updates lo hi = ok true) :
    BulkRangeOn Q mapInst updates factor depth start := by
  intro queryLo queryHi hquery
  exact hself queryLo queryHi (.left_tail hlo hhi hhas hquery)

theorem BulkRangeOn.right {T U : Type} {Q : Std.Usize → Std.Usize → Prop}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat} {lo hi : Std.Usize}
    (hself : BulkRangeOn Q mapInst updates factor (depth + 1) start)
    (hlo : lo.val = start + subtreeCapacity factor depth)
    (hhi : hi.val = start + subtreeCapacity factor depth + subtreeCapacity factor depth)
    (hhas : mapInst.has_any_in_range updates lo hi = ok true) :
    BulkRangeOn Q mapInst updates factor depth (start + subtreeCapacity factor depth) := by
  intro queryLo queryHi hquery
  exact hself queryLo queryHi (.right_tail hlo hhi hhas hquery)

end milhouse.tree
