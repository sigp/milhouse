import Tree.ProgressiveList.PopFront.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Zero removal always succeeds. For nonzero removal, success requires and
is guaranteed by an in-bounds count, representable occupied retained layers,
successful retained clones, and successful default construction. Representation
is needed only for nonzero removal; layout and backing traversal invariants
are needed only for an in-bounds rebuild. No clone identity or semantic law for
the default map is required. -/
theorem ProgressiveList.pop_front_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : n ≠ 0#usize → self.Represents ValueInst mapInst contents)
    (hlayout : n ≠ 0#usize → n.val ≤ contents.length → tree.PackingLayout ValueInst factor packingDepth)
    (hbacking : n ≠ 0#usize → n.val ≤ contents.length → self.BackingValid factor) :
    (∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result)) ↔
      n = 0#usize ∨ (n.val ≤ contents.length ∧
        ProgressiveTree.LengthFits factor (contents.drop n.val).length ∧
        (∀ value ∈ contents.drop n.val,
          ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied) ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates) := by
  by_cases hzero : n = 0#usize
  · simp only [hzero, ProgressiveList.pop_front_zero, ok.injEq, Prod.mk.injEq, true_and,
      exists_eq', true_or]
  · simp only [hzero, false_or]
    constructor
    · rintro ⟨result, hpop⟩
      have hbound : n.val ≤ contents.length := by
        rcases ProgressiveList.pop_front_success_state ValueInst mapInst self n hpop with
          ⟨hzero', _⟩ | ⟨_, beforeLength, cursor, initial, built, output, length, updates,
            hlen, hindex, _⟩
        · exact (hzero hzero').elim
        · obtain ⟨observed, hobserved, hcontentsLength⟩ := (hrep hzero).1
          rw [hlen] at hobserved
          cases hobserved
          scalar_tac
      obtain ⟨_, hclones, hlength, hdefault, hvalid⟩ := ProgressiveList.pop_front_nonzero_clones
        ValueInst mapInst (hlayout hzero hbound) self contents n (hrep hzero)
          (hbacking hzero hbound) hzero hpop
      refine ⟨hbound, ?_, ?_, result.updates, hdefault⟩
      · simpa only [hlength] using hvalid.1.lengthFits hvalid.2
      · exact (milhouse_models.list_clone_success_iff ValueInst.corecloneCloneInst
          (contents.drop n.val)).mp ⟨result.tree.elements, hclones⟩
    · rintro ⟨hbound, hfits, hclone, updates, hdefault⟩
      obtain ⟨result, hpop, _, _, _⟩ := ProgressiveList.pop_front_nonzero_success
        ValueInst mapInst (hlayout hzero hbound) self contents n (hrep hzero)
          (hbacking hzero hbound) hzero hbound hclone hfits updates hdefault
      exact ⟨result, hpop⟩

end milhouse.progressive_list
