import Tree.BulkUpdate.RangeScope
import Tree.UpdateMap.RangeExtent

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Reflection on reached binary queries supplies the weaker numeric extent
conditions from a local dense update window. No global update-domain law is
needed outside that window. -/
theorem BulkRangeOn.preservesExtents_of_window {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start oldLength newLength : Nat}
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth start)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      start (subtreeCapacity factor depth) oldLength newLength) :
    BulkRangeOn (update_map.RangePreservesExtentAt mapInst updates
      (start + oldLength) (start + newLength)) mapInst updates factor depth start := by
  intro lo hi hquery
  have hbounds := hquery.bounds
  have hmono := hwindow.length_mono
  constructor
  · intro hfalse
    by_contra hne
    let index := max (start + oldLength) lo.val
    have hlo : lo.val ≤ index := by dsimp [index]; omega
    have hhi : index < hi.val := by dsimp [index]; omega
    have hnew : index < start + newLength := by dsimp [index]; omega
    have hold : start + oldLength ≤ index := Nat.le_max_left _ _
    have hhas := hwindow.extension_complete (index - start) (by omega) (by omega)
    have heq : start + (index - start) = index := by omega
    rw [heq] at hhas
    have htrue := (hrange lo hi hquery false hfalse).mpr ⟨index, hlo, hhi, hhas⟩
    cases htrue
  · intro htrue
    obtain ⟨index, hlo, hhi, hhas⟩ := (hrange lo hi hquery true htrue).mp rfl
    have heq : start + (index - start) = index := by omega
    have hbound := hwindow.updates_bounded (index - start) (by omega) (by rwa [heq])
    omega

end milhouse.tree
