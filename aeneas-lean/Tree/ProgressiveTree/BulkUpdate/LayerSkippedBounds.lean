import Tree.ProgressiveTree.BulkUpdate.LayerSkipped

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- A skipped zero layer cannot contain any part of the new logical prefix:
extension completeness would supply a pending value, while skipped-layer
agreement would require that value to be returned by the zero tree. -/
theorem ProgressiveTree.length_le_of_empty_zero_layer_of_agreement {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength : Nat} {newLength : Std.Usize}
    {depth next : Std.U32} {start stop binary : Std.Usize}
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hagreement : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerSkippedValuesAgree
      ValueInst mapInst updates maximum newLength.val depth)
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength.val)
    (hends : oldLength ≤ progressiveCapacity factor depth.val)
    (hempty : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
    newLength.val ≤ progressiveCapacity factor depth.val := by
  by_contra hnot
  obtain ⟨actualStart, hactualStart, hstartVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
  rw [hgeometry.start_eq] at hactualStart
  cases hactualStart
  rw [min_eq_right (by scalar_tac)] at hstartVal
  have hnonempty := ProgressiveTree.layer_nonempty ValueInst hlayout
    hgeometry.next_eq hgeometry.start_eq hgeometry.stop_eq (by scalar_tac)
  obtain ⟨value, hget⟩ := hcomplete start (by omega) (by omega)
  have hread := hagreement.zero_here hgeometry hempty start value (Nat.le_refl _) hnonempty (by omega) hget
  simp only [ProgressiveTree.get_recursive] at hread
  cases hread

end milhouse.progressive_tree
