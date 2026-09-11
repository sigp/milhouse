import Tree.UpdateMap.MaxMap.Operations

open Aeneas Aeneas.Std Result

namespace milhouse.update_map

/-- The extracted trait default tests the actual length result. This equation
also preserves length failure and divergence; it says nothing about overrides. -/
theorem UpdateMap.is_empty_default_eq {T M : Type} (mapInst : UpdateMap M T) (self : M) :
    UpdateMap.is_empty.default mapInst self = (do
      let length ← mapInst.len self
      ok (decide (length = 0#usize))) := rfl

namespace MaxMap

/-- The actual MaxMap dictionary uses the trait default and forwards length
to the inner map. No law about the inner is_empty or maximum query is needed. -/
theorem is_empty_eq {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M) :
    (Insts.MilhouseUpdate_mapUpdateMap mapInst).is_empty self = (do
      let length ← mapInst.len self.inner
      ok (decide (length = 0#usize))) := rfl

/-- The concrete Rust caller reaches exactly the dictionary operation. -/
theorem is_empty_caller_eq {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M) :
    milhouse.proof_roots.max_map_is_empty mapInst self =
      (Insts.MilhouseUpdate_mapUpdateMap mapInst).is_empty self := rfl

/-- A known inner length supplies the wrapper's emptiness result without a
separate emptiness hypothesis or cache-validity invariant. -/
theorem is_empty_of_len {T M : Type} (mapInst : UpdateMap M T) (self : MaxMap M)
    (length : Std.Usize) (hlen : mapInst.len self.inner = ok length) :
    (Insts.MilhouseUpdate_mapUpdateMap mapInst).is_empty self =
      ok (decide (length = 0#usize)) := by
  rw [is_empty_eq, hlen]
  rfl

/-- Actual default construction with zero inner length establishes an empty
wrapper. No separate empty-default law is assumed for either map. -/
theorem default_is_empty_of_len {T M : Type} (mapInst : UpdateMap M T) (inner : M)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok inner)
    (hlen : mapInst.len inner = ok 0#usize) :
    ∃ self, (Insts.MilhouseUpdate_mapUpdateMap mapInst).coredefaultDefaultInst.default = ok self ∧
      (Insts.MilhouseUpdate_mapUpdateMap mapInst).is_empty self = ok true := by
  refine ⟨⟨inner, .Empty⟩, ?_, ?_⟩
  · change Insts.CoreDefaultDefault.default mapInst.coredefaultDefaultInst = _
    rw [default_eq, hdefault]
    rfl
  · exact is_empty_of_len mapInst _ 0#usize hlen

end MaxMap
end milhouse.update_map
