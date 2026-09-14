import Tree.BulkUpdate.Activation
import Tree.BulkUpdate.RangeScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- The missing-update guards along the selected binary traversal pass:
an unpacked terminal has a pending value, and an internal node never receives
two false child answers. Selected children satisfy the same condition. Packed
terminals need no pending value. This uses input observations only, without
an update result, range correctness, or range-query termination law. -/
def BulkGuardsPass {T U : Type} (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) : (depth start : Nat) → Prop
  | 0, start => factor = none → update_map.HasValueAt mapInst updates start
  | child + 1, start =>
    ∀ (lo middle stop : Std.Usize), lo.val = start →
      middle.val = start + subtreeCapacity factor child →
      stop.val = start + subtreeCapacity factor child + subtreeCapacity factor child →
      (¬ (mapInst.has_any_in_range updates lo middle = ok false ∧
        mapInst.has_any_in_range updates middle stop = ok false)) ∧
      (mapInst.has_any_in_range updates lo middle = ok true → BulkGuardsPass mapInst updates factor child start) ∧
      (mapInst.has_any_in_range updates middle stop = ok true →
        BulkGuardsPass mapInst updates factor child (start + subtreeCapacity factor child))

/-- Pending-value activation and range reflection imply the actual guard
condition, without assuming range-query termination. -/
theorem BulkGuardsPass.of_enabled {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {factor : Option Std.Usize}
    {depth start : Nat}
    (henabled : BulkUpdateEnabled mapInst updates factor depth start)
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth start) :
    BulkGuardsPass mapInst updates factor depth start := by
  induction depth generalizing start with
  | zero =>
    intro hnone
    subst factor
    obtain ⟨index, hindex, hhas⟩ := henabled.has_value_of_unpacked
    have hz : index = 0 := by simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hindex; omega
    simpa only [hz, Nat.add_zero] using hhas
  | succ child ih =>
    intro lo middle stop hlo hmiddle hstop
    have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
    have hleft := hrange.left_query hlo hmiddle
    have hright := hrange.right_query (lo := middle) (hi := stop) hmiddle hstop
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hfalseLeft, hfalseRight⟩
      obtain ⟨index, hindex, hvalue⟩ := henabled.has_value_of_depth_ne_zero (by omega)
      by_cases hlow : start + index < middle.val
      · have hbad := (hleft false hfalseLeft).mpr ⟨start + index, by omega, hlow, hvalue⟩
        cases hbad
      · have hbad := (hright false hfalseRight).mpr ⟨start + index, by omega, by omega, hvalue⟩
        cases hbad
    · intro hselected
      obtain ⟨index, hlow, hhigh, hvalue⟩ := (hleft true hselected).mp rfl
      apply ih ?_ (hrange.left hlo hmiddle hselected)
      refine Or.inr ⟨index - start, by omega, ?_⟩
      have heq : start + (index - start) = index := by omega
      rwa [heq]
    · intro hselected
      obtain ⟨index, hlow, hhigh, hvalue⟩ := (hright true hselected).mp rfl
      apply ih ?_ (hrange.right (lo := middle) (hi := stop) hmiddle hstop hselected)
      refine Or.inr ⟨index - (start + subtreeCapacity factor child), by omega, ?_⟩
      have heq : start + subtreeCapacity factor child + (index - (start + subtreeCapacity factor child)) = index := by omega
      rwa [heq]

end milhouse.tree
