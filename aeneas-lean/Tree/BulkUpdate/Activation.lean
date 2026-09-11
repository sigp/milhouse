import Tree.UpdateMap.Domain

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- A pending-value start condition used with range reflection. An unpacked
leaf or internal binary node is activated by a pending value; a packed terminal
may also scan without one. Actual internal guards concern child range answers,
so necessity of this value-based condition uses positive range witnesses. -/
def BulkUpdateEnabled {T U : Type} (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (depth start : Nat) : Prop :=
  (depth = 0 ∧ factor ≠ none) ∨
    ∃ index, index < subtreeCapacity factor depth ∧
      update_map.HasValueAt mapInst updates (start + index)

theorem BulkUpdateEnabled.has_value_of_unpacked {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {depth start : Nat}
    (h : BulkUpdateEnabled mapInst updates none depth start) :
    ∃ index, index < subtreeCapacity none depth ∧
      update_map.HasValueAt mapInst updates (start + index) := by
  rcases h with ⟨_, hnone⟩ | h
  · exact False.elim (hnone rfl)
  · exact h

theorem BulkUpdateEnabled.has_value_of_depth_ne_zero {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor : Option Std.Usize} {depth start : Nat}
    (h : BulkUpdateEnabled mapInst updates factor depth start) (hdepth : depth ≠ 0) :
    ∃ index, index < subtreeCapacity factor depth ∧
      update_map.HasValueAt mapInst updates (start + index) := by
  rcases h with ⟨hzero, _⟩ | h
  · exact False.elim (hdepth hzero)
  · exact h

end milhouse.tree
