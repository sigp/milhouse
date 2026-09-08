import Tree.ProgressiveList.Push

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Observable representation of a finite sequence: length and every
    machine-indexed lookup agree with the sequence, including out-of-bounds
    reads. This is separate from the structural tree invariants needed to
    justify rebuilding and bulk updates. -/
def ProgressiveList.Represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) : Prop :=
  (∃ length, ProgressiveList.len ValueInst mapInst self = ok length ∧
    length.val = contents.length) ∧
  ∀ index, ProgressiveList.get ValueInst mapInst self index = ok contents[index.val]?

/-- Empty construction represents the empty sequence. All requirements on
    the generic default map are stated explicitly as empty-map laws. -/
theorem ProgressiveList.empty_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ i, mapInst.get updates i = ok none)
    (hmax : mapInst.max_index updates = ok none) :
    ∃ self, ProgressiveList.empty ValueInst mapInst = ok self ∧
      self.Represents ValueInst mapInst [] := by
  let self : ProgressiveList T U :=
    { tree := .ProgressiveZero, length := 0#usize, updates }
  refine ⟨self, ProgressiveList.empty_eq ValueInst mapInst updates hdefault,
    ⟨⟨0#usize, ProgressiveList.len_of_no_max_index ValueInst mapInst self hmax, rfl⟩,
      ?_⟩⟩
  intro i
  exact ProgressiveList.get_none_of_backing_bound ValueInst mapInst self i
    (hget i) (by simp [self])

/-- `Default::default` represents the empty sequence under the same map laws. -/
theorem ProgressiveList.default_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ i, mapInst.get updates i = ok none)
    (hmax : mapInst.max_index updates = ok none) :
    ∃ self, ProgressiveList.Insts.CoreDefaultDefault.default ValueInst mapInst = ok self ∧
      self.Represents ValueInst mapInst [] := by
  rw [ProgressiveList.default_eq_empty]
  exact ProgressiveList.empty_represents ValueInst mapInst updates hdefault hget hmax

end milhouse.progressive_list
