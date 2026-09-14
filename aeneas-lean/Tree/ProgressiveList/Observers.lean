import Tree.ProgressiveList

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- With no pending map entries, the logical length equals the backing
    length. Only the answer of `max_index` is relevant to this observer. -/
theorem ProgressiveList.len_of_no_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U)
    (hmax : mapInst.max_index self.updates = ok none) :
    ProgressiveList.len ValueInst mapInst self = ok self.length := by
  simp [ProgressiveList.len, utils.updated_length, hmax,
    core.option.Option.map_or, utils.Length.as_usize]

/-- `is_empty` reports exactly whether the observed logical length is zero. -/
theorem ProgressiveList.is_empty_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (length : Std.Usize)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length) :
    ProgressiveList.is_empty ValueInst mapInst self =
      ok (decide (length = 0#usize)) := by
  simp [ProgressiveList.is_empty, hlen]

/-- Pending-update detection is the negation of the map's emptiness answer. -/
theorem ProgressiveList.has_pending_updates_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (empty : Bool)
    (hempty : mapInst.is_empty self.updates = ok empty) :
    ProgressiveList.has_pending_updates ValueInst mapInst self = ok (!empty) := by
  simp [ProgressiveList.has_pending_updates, hempty]

/-- Without an update at the queried index, indices beyond the backing
    length return `none`; the backing tree is not consulted. -/
theorem ProgressiveList.get_none_of_backing_bound {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hget : mapInst.get self.updates index = ok none)
    (hindex : ¬ index < self.length) :
    ProgressiveList.get ValueInst mapInst self index = ok none := by
  simp only [ProgressiveList.get, hget, bind_tc_ok, ProgressiveList.backing_get,
    ProgressiveList.backing_len, utils.Length.as_usize, if_neg hindex]

/-- `empty` has a zero backing tree and backing length, and uses the default
    update map. This statement also identifies the exact returned state. -/
theorem ProgressiveList.empty_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.empty ValueInst mapInst =
      ok { tree := .ProgressiveZero, length := 0#usize, updates } := by
  simp [ProgressiveList.empty, progressive_tree.ProgressiveTree.empty,
    triomphe.arc.Arc.new, hdefault]

/-- Default construction has exactly the behavior of `empty`, including
    failure of a user-supplied update-map default implementation. -/
theorem ProgressiveList.default_eq_empty {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.CoreDefaultDefault.default ValueInst mapInst =
      ProgressiveList.empty ValueInst mapInst := rfl

/-- Full observer specification for an empty list. The default map needs
    exactly the empty-map laws used by these observers; no element or
    backing-tree assumptions are needed. -/
theorem ProgressiveList.empty_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ i, mapInst.get updates i = ok none)
    (hmax : mapInst.max_index updates = ok none)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.empty ValueInst mapInst = ok self ∧
      ProgressiveList.len ValueInst mapInst self = ok 0#usize ∧
      ProgressiveList.is_empty ValueInst mapInst self = ok true ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false ∧
      ∀ i, ProgressiveList.get ValueInst mapInst self i = ok none := by
  let self : ProgressiveList T U :=
    { tree := .ProgressiveZero, length := 0#usize, updates }
  have hlen := ProgressiveList.len_of_no_max_index ValueInst mapInst self hmax
  refine ⟨self, ProgressiveList.empty_eq ValueInst mapInst updates hdefault,
    hlen, ?_, ?_, ?_⟩
  · exact ProgressiveList.is_empty_spec ValueInst mapInst self 0#usize hlen
  · exact ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty
  · intro i
    exact ProgressiveList.get_none_of_backing_bound ValueInst mapInst self i
      (hget i) (by simp [self])

end milhouse.progressive_list
