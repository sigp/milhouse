import Tree.ProgressiveList.Contents
import Tree.ProgressiveTree.Lookup

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Pending values override the corresponding backing values to give the
    represented sequence. All required map reads succeed, including missing
    entries and indices outside the sequence. -/
def ProgressiveListIter.Overlay {T U : Type} (mapInst : update_map.UpdateMap U T)
    (updates : U) (backing contents : _root_.List T) : Prop :=
  ∀ index : Std.Usize, ∃ pending, mapInst.get updates index = ok pending ∧
    pending.or backing[index.val]? = contents[index.val]?

/-- The bounded backing read agrees with ordinary sequence indexing, including
    missing indices after the backing length. -/
theorem ProgressiveList.backing_get_eq_elements {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U)
    (hdense : self.tree.Dense factor 0 self.length.val)
    (hfits : self.tree.Fits factor 0) (index : Std.Usize) :
    ProgressiveList.backing_get ValueInst mapInst self index = ok self.tree.elements[index.val]? := by
  simp only [ProgressiveList.backing_get, ProgressiveList.backing_len,
    utils.Length.as_usize, bind_tc_ok]
  by_cases hinside : index < self.length
  · rw [if_pos hinside]
    simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok]
    simpa [progressiveCapacity] using
      hdense.get_recursive_eq_elements ValueInst hlayout hfits index (depth := 0#u32)
  · rw [if_neg hinside]
    have hbound : self.tree.elements.length ≤ index.val := by
      have hle := (UScalar.le_equiv _ _).mp (le_of_not_gt hinside)
      rw [hdense.elements_length]
      exact hle
    rw [_root_.List.getElem?_eq_none_iff.mpr hbound]

/-- A represented list already supplies the pending/backing overlay law needed
    by iteration. No additional assumptions about map reads or missing-entry
    behavior are required beyond the existing representation. -/
theorem ProgressiveList.Represents.overlay {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ProgressiveListIter.Overlay mapInst self.updates self.tree.elements contents := by
  intro index
  have hread := hrep.2 index
  cases hmap : mapInst.get self.updates index with
  | fail e => simp [ProgressiveList.get, hmap] at hread
  | div => simp [ProgressiveList.get, hmap] at hread
  | ok pending =>
    refine ⟨pending, rfl, ?_⟩
    cases pending with
    | none =>
      rw [ProgressiveList.get, hmap] at hread
      simp only [bind_tc_ok] at hread
      rw [ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout self hdense hfits index] at hread
      exact Result.ok.inj hread
    | some value => simpa [ProgressiveList.get, hmap, Option.or] using hread

end milhouse.progressive_list
