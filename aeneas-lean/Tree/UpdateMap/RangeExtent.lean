import Tree.UpdateMap.Range
import Tree.BulkUpdate.Window

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- Numeric effects required of a range answer by density preservation.
A skipped interval retains its occupied length; a selected interval starts
inside the final prefix. No pending-value witness or absence law is required. -/
structure RangePreservesExtentAt {T U : Type} (mapInst : UpdateMap U T) (updates : U)
    (oldLength newLength : Nat) (lo hi : Std.Usize) : Prop where
  empty_length : mapInst.has_any_in_range updates lo hi = ok false →
    min (newLength - lo.val) (hi.val - lo.val) = min (oldLength - lo.val) (hi.val - lo.val)
  selected_inside : mapInst.has_any_in_range updates lo hi = ok true → lo.val < newLength

/-- Correct range reflection supplies the weaker numeric conditions from
the actual dense update domain. Queries outside the final prefix cannot be
positive; empty answers need only preserve the interval's occupied length. -/
theorem RangeReflectsValuesAt.preservesExtent {T U : Type}
    {mapInst : UpdateMap U T} {updates : U} {oldLength newLength : Nat}
    {lo hi : Std.Usize}
    (h : RangeReflectsValuesAt mapInst updates lo hi)
    (hdomain : tree.DenseUpdateDomain oldLength newLength (HasValueAt mapInst updates)) :
    RangePreservesExtentAt mapInst updates oldLength newLength lo hi := by
  constructor
  · intro hempty
    apply (hdomain.window lo.val (hi.val - lo.val)).length_eq_of_empty (Nat.min_le_right _ _)
    rintro ⟨index, hindex, hhas⟩
    have htrue := (h false hempty).mpr ⟨lo.val + index, by omega, by omega, hhas⟩
    cases htrue
  · intro hselected
    obtain ⟨index, hlo, _, hhas⟩ := (h true hselected).mp rfl
    have := hdomain.updates_bounded index hhas
    omega

end milhouse.update_map
