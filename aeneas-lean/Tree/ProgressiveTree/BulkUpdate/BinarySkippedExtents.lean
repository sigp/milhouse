import Tree.BulkUpdate.SkippedExtents
import Tree.ProgressiveTree.BulkUpdate.BinarySkipped

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- A skipped range inside a selected binary layer retains its occupied
extent when its pending values match the original slots. Pure slot routing
uses input density and layout, without a capacity, clone, range-value, or
successful-update law. -/
theorem ProgressiveTree.BulkBinarySkippedValuesAgree.empty_length {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength newLength : Nat}
    {self : ProgressiveTree T} {depth : Std.U32}
    {layer : tree.Tree T} {start binary lo hi : Std.Usize}
    (hagreement : self.BulkBinarySkippedValuesAgree ValueInst mapInst updates factor maximum depth)
    (hdense : self.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val))
    (hmono : oldLength ≤ newLength)
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength)
    (hvisit : self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary)
    (hquery : tree.BulkRangeQueried mapInst updates factor binary.val start.val lo hi)
    (hfalse : mapInst.has_any_in_range updates lo hi = ok false) :
    min (newLength - lo.val) (hi.val - lo.val) = min (oldLength - lo.val) (hi.val - lo.val) := by
  by_contra hne
  have hbounds := hquery.bounds
  have hbound : max oldLength lo.val < 2 ^ UScalarTy.Usize.numBits := by
    have : max oldLength lo.val < hi.val := by omega
    scalar_tac
  let query := Std.Usize.ofNatCore (max oldLength lo.val) hbound
  have hqueryVal : query.val = max oldLength lo.val := Usize.ofNatCore_val_eq hbound
  have hlo : lo.val ≤ query.val := by omega
  have hhi : query.val < hi.val := by omega
  obtain ⟨value, hget⟩ := hcomplete query (by omega) (by omega)
  have hagree := hagreement layer start binary hvisit lo hi
    (by simpa only [Nat.zero_add] using hquery) hfalse query value hlo hhi hget
  rw [← hvisit.slot_before_eq_layer hlayout (by omega) (by omega)] at hagree
  obtain ⟨layerDepth, hdepth, hstart, _⟩ := hvisit.position hlayout
  have hrootLo := progressiveCapacity_mono factor hdepth
  rw [← hstart] at hrootLo
  have hread := hdense.slot_eq_elements (query.val - progressiveCapacity factor depth.val)
  have hnone : self.elements[query.val - progressiveCapacity factor depth.val]? = none :=
    _root_.List.getElem?_eq_none (by rw [hdense.elements_length]; omega)
  rw [hnone] at hread
  rw [hread] at hagree
  cases hagree

/-- Binary skipped-value agreement supplies all false-answer extent laws.
Only positive answers retain an independent numeric selection condition. -/
theorem ProgressiveTree.BulkBinarySkippedValuesAgree.preservesExtents {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength newLength : Nat}
    {self : ProgressiveTree T} {depth : Std.U32}
    (hagreement : self.BulkBinarySkippedValuesAgree ValueInst mapInst updates factor maximum depth)
    (hdense : self.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val))
    (hmono : oldLength ≤ newLength)
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength)
    (hselected : self.BulkBinaryRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
      ValueInst mapInst updates factor maximum depth) :
    self.BulkBinaryRangeOn (update_map.RangePreservesExtentAt mapInst updates oldLength newLength)
      ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit lo hi hquery
  exact ⟨hagreement.empty_length hlayout hdense hmono hcomplete hvisit hquery,
    hselected layer start binary hvisit lo hi hquery⟩

end milhouse.progressive_tree
