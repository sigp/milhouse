import Tree.ProgressiveList.PopFront.Clones

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful front removal preserves backing density and representable
    capacities, without assumptions about iterator contents, map laws, or clone
    identity. Rebuilding establishes these properties from a fresh builder;
    packing layout is needed only for a nonzero removal. -/
theorem ProgressiveList.pop_front_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (self : ProgressiveList T U) (n : Std.Usize)
    (hlayout : n ≠ 0#usize → tree.PackingLayout ValueInst factor packingDepth)
    (hbacking : self.BackingValid factor)
    {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    result.BackingValid factor := by
  rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
    ⟨_, rfl⟩ | ⟨hnonzero, beforeLength, cursor, initial, built, output, length, updates,
      _, _, _, hnew, hextend, hfinish, _, rfl⟩
  · exact hbacking
  · have hinitial := ProgressiveTreeBuilder.new_valid ValueInst (hlayout hnonzero) hnew
    have hbuilt := ProgressiveListIter.extend_builder_preserves_valid ValueInst mapInst cursor initial hinitial hextend
    exact (ProgressiveTreeBuilder.finish_spec ValueInst built hbuilt hfinish).2.2

/-- Successful `pop_front n` represents exactly the old sequence with its first
    `n` values removed, with a valid backing tree. A nonzero removal clears
    pending updates. Clone identity is needed only for the retained suffix;
    iterator completeness and every indexed-read bound are derived internally.
    Packing, clone, and default-map laws apply only to nonzero removal. -/
theorem ProgressiveList.pop_front_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hlayout : n ≠ 0#usize → tree.PackingLayout ValueInst factor packingDepth)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hclone : n ≠ 0#usize → ∀ value ∈ contents.drop n.val,
      ValueInst.corecloneCloneInst.clone value = ok value)
    (hdefault : n ≠ 0#usize → ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ i, mapInst.get updates i = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      (n ≠ 0#usize → ProgressiveList.has_pending_updates ValueInst mapInst result = ok false) := by
  by_cases hzero : n = 0#usize
  · subst n
    have heq : self = result := by
      simpa only [ProgressiveList.pop_front_zero, ok.injEq, Prod.mk.injEq, true_and] using hpop
    subst result
    exact ⟨by simpa using hrep, hbacking, by simp⟩
  · obtain ⟨_, hclones, _, hmap, hvalid⟩ := ProgressiveList.pop_front_nonzero_clones
      ValueInst mapInst (hlayout hzero) self contents n hrep hbacking hzero hpop
    have hidentity := milhouse_models.list_clone_identity ValueInst.corecloneCloneInst
      (contents.drop n.val) (hclone hzero)
    have helements : result.tree.elements = contents.drop n.val :=
      Result.ok.inj (hclones.symm.trans hidentity)
    obtain ⟨hget, hmax, hempty⟩ := hdefault hzero result.updates hmap
    refine ⟨?_, hvalid, fun _ => ProgressiveList.has_pending_updates_spec
      ValueInst mapInst result true hempty⟩
    rw [← helements]
    exact ProgressiveList.represents_of_dense_backing ValueInst mapInst (hlayout hzero)
      result hvalid.1 hvalid.2 hget hmax

end milhouse.progressive_list
