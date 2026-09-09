import Tree.ProgressiveTree.BulkUpdate.LayerSkippedReads
import Tree.ProgressiveTree.Lookup

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Agreement in a skipped layer forces its occupied length to stay the
same: otherwise an extension value would have to agree with a missing input
backing read. Only input invariants and the actual false answer are used. -/
theorem ProgressiveTree.BulkLayerSkippedValuesAgree.empty_length {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength newLength : Nat}
    {self : ProgressiveTree T} {depth : Std.U32} {start stop : Std.Usize}
    (hagreement : self.BulkLayerSkippedValuesAgree ValueInst mapInst updates maximum newLength depth)
    (hdense : self.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val))
    (hfits : self.Fits factor depth.val) (hmono : oldLength ≤ newLength)
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength)
    (hquery : self.BulkLayerRangeQueried ValueInst mapInst updates maximum depth start stop)
    (hfalse : mapInst.has_any_in_range updates start stop = ok false) :
    min (newLength - start.val) (stop.val - start.val) =
      min (oldLength - start.val) (stop.val - start.val) := by
  by_contra hnot
  have hnonempty : start < stop := (UScalar.lt_equiv _ _).mpr hquery.nonempty
  have hfalse' : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false := by
    simp only [ProgressiveTree.has_updates_in_range, if_pos hnonempty, hfalse]
  obtain ⟨layer, layerDepth, hskip⟩ := hquery.skipped_of_false hfalse'
  have hbound : max oldLength start.val < 2 ^ UScalarTy.Usize.numBits := by
    have : max oldLength start.val < stop.val := by omega
    scalar_tac
  let query := Std.Usize.ofNatCore (max oldLength start.val) hbound
  have hqueryVal : query.val = max oldLength start.val := Usize.ofNatCore_val_eq hbound
  have hlo : start.val ≤ query.val := by omega
  have hhi : query.val < stop.val := by omega
  have hnew : query.val < newLength := by omega
  obtain ⟨value, hget⟩ := hcomplete query (by omega) hnew
  have hagree := hagreement layer layerDepth start stop hskip query value hlo hhi hnew hget
  rw [← hskip.get_before_eq_layer hlo] at hagree
  have hread := hdense.get_recursive_eq_elements ValueInst hlayout hfits query
  have hnone : self.elements[query.val - progressiveCapacity factor depth.val]? = none :=
    _root_.List.getElem?_eq_none (by rw [hdense.elements_length]; omega)
  rw [hnone] at hread
  rw [hread] at hagree
  cases hagree

/-- Skipped-layer agreement supplies the false-answer extent law, leaving
only the positive-answer condition as an independent range premise. -/
theorem ProgressiveTree.BulkLayerSkippedValuesAgree.preservesExtents {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength newLength : Nat}
    {self : ProgressiveTree T} {depth : Std.U32}
    (hagreement : self.BulkLayerSkippedValuesAgree ValueInst mapInst updates maximum newLength depth)
    (hdense : self.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val))
    (hfits : self.Fits factor depth.val) (hmono : oldLength ≤ newLength)
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength)
    (hselected : self.BulkLayerRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
      ValueInst mapInst updates maximum depth) :
    self.BulkLayerRangeOn (update_map.RangePreservesExtentAt mapInst updates oldLength newLength)
      ValueInst mapInst updates maximum depth := by
  intro start stop hquery
  exact ⟨hagreement.empty_length hlayout hdense hfits hmono hcomplete hquery,
    hselected start stop hquery⟩

end milhouse.progressive_tree
