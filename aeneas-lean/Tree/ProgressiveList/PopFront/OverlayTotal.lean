import Tree.ProgressiveList.PopFront.Conditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful nonzero removal represents the retained source suffix exactly
when the removal bound and retained capacity hold and the actual ordered
clones/default map have the required overlay and logical extent. Clone identity,
absent map entries, and an absent maximum are not necessary. -/
theorem ProgressiveList.pop_front_nonzero_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor) (hnonzero : n ≠ 0#usize) :
    (∃ result, ProgressiveList.pop_front ValueInst mapInst self n = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val)) ↔
      n.val ≤ contents.length ∧ ProgressiveTree.LengthFits factor (contents.drop n.val).length ∧
      ∃ copied updates, _root_.List.mapM ValueInst.corecloneCloneInst.clone (contents.drop n.val) = ok copied ∧
        mapInst.coredefaultDefaultInst.default = ok updates ∧
        (∃ largest, mapInst.max_index updates = ok largest ∧
          largest.elim (contents.drop n.val).length
            (fun index => max (index.val + 1) (contents.drop n.val).length) = (contents.drop n.val).length) ∧
        ProgressiveListIter.Overlay mapInst updates copied (contents.drop n.val) := by
  constructor
  · rintro ⟨result, hpop, hresult⟩
    obtain ⟨hbound, hclones, hlength, hdefault, hvalid⟩ := ProgressiveList.pop_front_nonzero_clones
      ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
    refine ⟨hbound, ?_, result.tree.elements, result.updates, hclones, hdefault,
      (ProgressiveList.pop_front_nonzero_represents_iff ValueInst mapInst hlayout
        self contents n hrep hbacking hnonzero hpop).mp hresult⟩
    simpa only [hlength] using hvalid.1.lengthFits hvalid.2
  · rintro ⟨hbound, hfits, copied, updates, hclones, hdefault, hextent, hoverlay⟩
    have hclone := (milhouse_models.list_clone_success_iff ValueInst.corecloneCloneInst
      (contents.drop n.val)).mp ⟨copied, hclones⟩
    obtain ⟨result, hpop, _, _, hupdates⟩ := ProgressiveList.pop_front_nonzero_success
      ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hbound hclone hfits updates hdefault
    obtain ⟨_, hactual, _, _, _⟩ := ProgressiveList.pop_front_nonzero_clones
      ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
    have helements : result.tree.elements = copied := Result.ok.inj (hactual.symm.trans hclones)
    refine ⟨result, hpop, (ProgressiveList.pop_front_nonzero_represents_iff ValueInst mapInst hlayout
      self contents n hrep hbacking hnonzero hpop).mpr ?_⟩
    simpa only [hupdates, helements] using And.intro hextent hoverlay

/-- The public success-and-representation criterion also covers the zero
no-op. Packing and traversal laws apply only to a nonzero in-bounds rebuild;
all clone and default-map obligations are omitted on zero removal. -/
theorem ProgressiveList.pop_front_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hlayout : n ≠ 0#usize → n.val ≤ contents.length → tree.PackingLayout ValueInst factor packingDepth)
    (hbacking : n ≠ 0#usize → n.val ≤ contents.length → self.BackingValid factor) :
    (∃ result, ProgressiveList.pop_front ValueInst mapInst self n = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val)) ↔
      n = 0#usize ∨ (n.val ≤ contents.length ∧ ProgressiveTree.LengthFits factor (contents.drop n.val).length ∧
      ∃ copied updates, _root_.List.mapM ValueInst.corecloneCloneInst.clone (contents.drop n.val) = ok copied ∧
        mapInst.coredefaultDefaultInst.default = ok updates ∧
        (∃ largest, mapInst.max_index updates = ok largest ∧
          largest.elim (contents.drop n.val).length
            (fun index => max (index.val + 1) (contents.drop n.val).length) = (contents.drop n.val).length) ∧
        ProgressiveListIter.Overlay mapInst updates copied (contents.drop n.val)) := by
  by_cases hzero : n = 0#usize
  · subst n
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact ⟨self, ProgressiveList.pop_front_zero ValueInst mapInst self, by simpa using hrep⟩
  · simp only [hzero, false_or]
    constructor
    · rintro ⟨result, hpop, hresult⟩
      have hsuccess := (ProgressiveList.pop_front_success_iff ValueInst mapInst self contents n
        (fun _ => hrep) hlayout hbacking).mp ⟨result, hpop⟩
      have hbound : n.val ≤ contents.length := (hsuccess.resolve_left hzero).1
      exact (ProgressiveList.pop_front_nonzero_success_represents_iff ValueInst mapInst (hlayout hzero hbound)
        self contents n hrep (hbacking hzero hbound) hzero).mp ⟨result, hpop, hresult⟩
    · intro hinputs
      exact (ProgressiveList.pop_front_nonzero_success_represents_iff ValueInst mapInst (hlayout hzero hinputs.1)
        self contents n hrep (hbacking hzero hinputs.1) hzero).mpr hinputs

/-- Actual ordered clones and a default map with the matching overlay/extent
give the complete nonzero removal result. Pending emptiness is a separate law
used only for that observer. Every iterator/builder/default call and the exact
installed backing and map are established internally. -/
theorem ProgressiveList.pop_front_nonzero_overlay_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) (hbound : n.val ≤ contents.length)
    (hfits : ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (copied : _root_.List T) (updates : U)
    (hclones : _root_.List.mapM ValueInst.corecloneCloneInst.clone (contents.drop n.val) = ok copied)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hextent : ∃ largest, mapInst.max_index updates = ok largest ∧
      largest.elim (contents.drop n.val).length
        (fun index => max (index.val + 1) (contents.drop n.val).length) = (contents.drop n.val).length)
    (hoverlay : ProgressiveListIter.Overlay mapInst updates copied (contents.drop n.val))
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ result, ProgressiveList.pop_front ValueInst mapInst self n = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst (contents.drop n.val) ∧ result.BackingValid factor ∧
      result.tree.elements = copied ∧ result.length.val = (contents.drop n.val).length ∧
      result.updates = updates ∧ ProgressiveList.has_pending_updates ValueInst mapInst result = ok false := by
  obtain ⟨result, hpop, hresult⟩ := (ProgressiveList.pop_front_nonzero_success_represents_iff ValueInst mapInst hlayout
    self contents n hrep hbacking hnonzero).mpr ⟨hbound, hfits, copied, updates, hclones, hdefault, hextent, hoverlay⟩
  obtain ⟨_, hactual, hlength, hmap, hvalid⟩ := ProgressiveList.pop_front_nonzero_clones
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
  have helements : result.tree.elements = copied := Result.ok.inj (hactual.symm.trans hclones)
  have hupdates : result.updates = updates := Result.ok.inj (hmap.symm.trans hdefault)
  exact ⟨result, hpop, hresult, hvalid, helements, hlength, hupdates,
    ProgressiveList.has_pending_updates_spec ValueInst mapInst result true (by simpa only [hupdates] using hempty)⟩

end milhouse.progressive_list
