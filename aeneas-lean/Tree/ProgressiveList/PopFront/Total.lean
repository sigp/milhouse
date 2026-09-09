import Tree.ProgressiveList.PopFront.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Nonzero front removal succeeds and returns exactly the retained suffix,
with valid rebuilt backing and no pending updates. Clone laws concern only
retained values, and capacity is needed only for that rebuilt suffix. Actual
iteration and every builder success are established internally. -/
theorem ProgressiveList.pop_front_nonzero_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) (hbound : n.val ≤ contents.length)
    (hclone : ∀ value ∈ contents.drop n.val, ValueInst.corecloneCloneInst.clone value = ok value)
    (hfits : ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  obtain ⟨result, hpop, _, _, _⟩ := ProgressiveList.pop_front_nonzero_success
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hbound
    (fun value hv => ⟨value, hclone value hv⟩) hfits updates hdefault
  have hdefaultLaws : ∀ actual, mapInst.coredefaultDefaultInst.default = ok actual →
      (∀ index, mapInst.get actual index = ok none) ∧
        mapInst.max_index actual = ok none ∧ mapInst.is_empty actual = ok true := by
    intro actual hactual
    rw [hdefault] at hactual
    cases hactual
    exact ⟨hget, hmax, hempty⟩
  obtain ⟨hcontents, hvalid, hpending⟩ := ProgressiveList.pop_front_spec
    ValueInst mapInst self contents n (fun _ => hlayout) hrep hbacking
    (fun _ => hclone) (fun _ => hdefaultLaws) hpop
  exact ⟨result, hpop, hcontents, hvalid, hpending hnonzero⟩

/-- Front removal within the logical length terminates and preserves exactly
the retained suffix. A zero removal is the original list and requires no packing,
clone, capacity, or default-map law. Nonzero removal rebuilds and clears pending
updates using only the retained values' laws and capacities. -/
theorem ProgressiveList.pop_front_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hlayout : n ≠ 0#usize → tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbound : n.val ≤ contents.length)
    (hclone : n ≠ 0#usize → ∀ value ∈ contents.drop n.val,
      ValueInst.corecloneCloneInst.clone value = ok value)
    (hfits : n ≠ 0#usize → ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (hdefault : n ≠ 0#usize → ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
      (∀ index, mapInst.get updates index = ok none) ∧
      mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true) :
    ∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      (n ≠ 0#usize → ProgressiveList.has_pending_updates ValueInst mapInst result = ok false) := by
  by_cases hzero : n = 0#usize
  · subst n
    refine ⟨self, ?_, ?_, hbacking, by simp⟩
    · simp only [ProgressiveList.pop_front, ↓reduceIte]
    · simpa only [show (0#usize).val = 0 from rfl, _root_.List.drop_zero] using hrep
  · obtain ⟨updates, hmap, hget, hmax, hempty⟩ := hdefault hzero
    obtain ⟨result, hpop, hcontents, hvalid, hpending⟩ :=
      ProgressiveList.pop_front_nonzero_total_spec ValueInst mapInst (hlayout hzero) self contents n hrep hbacking
        hzero hbound (hclone hzero) (hfits hzero) updates hmap hget hmax hempty
    exact ⟨result, hpop, hcontents, hvalid, fun _ => hpending⟩

end milhouse.progressive_list
