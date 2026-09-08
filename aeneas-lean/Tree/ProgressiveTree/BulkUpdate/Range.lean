import Tree.ProgressiveTree.Shape
import Tree.UpdateMap.Domain
import Tree.UpdateMap.Range

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

theorem ProgressiveTree.has_updates_in_range_true {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) {updates : U}
    {start stop : Std.Usize}
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    start.val < stop.val ∧ mapInst.has_any_in_range updates start stop = ok true := by
  unfold ProgressiveTree.has_updates_in_range at hhas
  split at hhas
  · exact ⟨by scalar_tac, hhas⟩
  · simp at hhas

theorem ProgressiveTree.has_updates_in_range_false_excludes {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) {updates : U}
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {start stop query : Std.Usize} {pending : Option T}
    (hempty : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false)
    (hget : mapInst.get updates query = ok pending)
    (hlo : start.val ≤ query.val) (hhi : query.val < stop.val) :
    pending = none := by
  have hnonempty : start < stop := by scalar_tac
  simp only [ProgressiveTree.has_updates_in_range, if_pos hnonempty] at hempty
  exact hrange start stop query pending hempty hget hlo hhi

/-- An empty first layer of a zero suffix precludes every dense extension
    into that suffix. The proof includes saturated endpoints and needs only
    the extension-completeness direction of update-domain validity. -/
theorem ProgressiveTree.length_le_of_empty_zero_layer {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) {updates : U}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {oldLength : Nat} {newLength : Std.Usize}
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength.val)
    {depth next : Std.U32} {start stop : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hends : oldLength ≤ progressiveCapacity factor depth.val)
    (hempty : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
    newLength.val ≤ progressiveCapacity factor depth.val := by
  by_contra hnot
  obtain ⟨actualStart, hactualStart, hstartVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
  rw [hstart] at hactualStart
  cases hactualStart
  rw [min_eq_right (by scalar_tac)] at hstartVal
  have hnonempty := ProgressiveTree.layer_nonempty ValueInst hlayout hnext hstart hstop (by scalar_tac)
  obtain ⟨value, hget⟩ := hcomplete start (by omega) (by omega)
  have hnone := ProgressiveTree.has_updates_in_range_false_excludes ValueInst mapInst hrange
    hempty hget (Nat.le_refl _) hnonempty
  cases hnone

end milhouse.progressive_tree
