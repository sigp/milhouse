import Tree.ProgressiveList.Construction.Conditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Iterator construction succeeds and represents its actual consumed
sequence exactly when the input has a finite yielding trace, occupied capacity
fits, and the actual default map preserves that sequence by overlay/extent.
No trace, map success, empty-map law, or internal execution is assumed. -/
theorem ProgressiveList.try_from_iter_success_represents_iff {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input = ok (.Ok self) ∧
      self.Represents ValueInst mapInst self.tree.elements) ↔
      ∃ values, IntoIteratorYields iterInst input values ∧ ProgressiveTree.LengthFits factor values.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
          (∃ largest, mapInst.max_index updates = ok largest ∧
            largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length) ∧
          ProgressiveListIter.Overlay mapInst updates values values := by
  constructor
  · rintro ⟨self, hnew, hrep⟩
    obtain ⟨hyields, hlength, hdefault⟩ := ProgressiveList.try_from_iter_trace ValueInst mapInst iterInst input hnew
    obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid ValueInst mapInst iterInst input hlayout hnew
    refine ⟨self.tree.elements, hyields, ?_, self.updates, hdefault,
      (ProgressiveList.try_from_iter_represents_iff ValueInst mapInst iterInst input
        self.tree.elements hyields hlayout hnew).mp hrep⟩
    simpa only [hlength] using hdense.lengthFits hfits
  · rintro ⟨values, hyields, hfits, updates, hdefault, hextent, hoverlay⟩
    obtain ⟨self, hnew, helements, _, hupdates, _⟩ := ProgressiveList.try_from_iter_total
      ValueInst mapInst iterInst input values hyields hlayout hfits updates hdefault
    have hrep : self.Represents ValueInst mapInst values :=
      (ProgressiveList.try_from_iter_represents_iff ValueInst mapInst iterInst input values hyields hlayout hnew).mpr
        (by simpa only [hupdates] using And.intro hextent hoverlay)
    exact ⟨self, hnew, by simpa only [helements] using hrep⟩

/-- Successful input-preserving vector construction requires and is ensured
by occupied capacity and an actual default map with the exact overlay/extent.
The vector's finite iterator is derived, not assumed. Pending emptiness is
irrelevant to this sequence criterion. -/
theorem ProgressiveList.new_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.new ValueInst mapInst values = ok (.Ok self) ∧
      self.Represents ValueInst mapInst values.val) ↔
      ProgressiveTree.LengthFits factor values.val.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
        (∃ largest, mapInst.max_index updates = ok largest ∧
          largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length) ∧
        ProgressiveListIter.Overlay mapInst updates values.val values.val := by
  constructor
  · rintro ⟨self, hnew, hrep⟩
    have hfits := ((ProgressiveList.new_success_iff ValueInst mapInst values hlayout).mp ⟨self, hnew⟩).1
    have hdefault := (ProgressiveList.new_contents ValueInst mapInst values hnew).2.2
    exact ⟨hfits, self.updates, hdefault,
      (ProgressiveList.new_represents_iff ValueInst mapInst values hlayout hnew).mp hrep⟩
  · rintro ⟨hfits, updates, hdefault, hextent, hoverlay⟩
    obtain ⟨self, hnew, _, _, hupdates, _⟩ := ProgressiveList.try_from_iter_total ValueInst mapInst
      (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values) hlayout hfits updates hdefault
    refine ⟨self, hnew, (ProgressiveList.new_represents_iff ValueInst mapInst values hlayout hnew).mpr ?_⟩
    simpa only [hupdates] using And.intro hextent hoverlay

/-- The concrete vector-conversion trait has the same complete criterion
for successful input representation as the inherent constructor. -/
theorem ProgressiveList.try_from_vec_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.CoreConvertTryFromVecError.try_from ValueInst mapInst values = ok (.Ok self) ∧
      self.Represents ValueInst mapInst values.val) ↔
      ProgressiveTree.LengthFits factor values.val.length ∧
      ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
        (∃ largest, mapInst.max_index updates = ok largest ∧
          largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length) ∧
        ProgressiveListIter.Overlay mapInst updates values.val values.val :=
  ProgressiveList.new_success_represents_iff ValueInst mapInst values hlayout

/-- The SSZ construction trait's successful representation of its actual
consumed sequence has the same trace/capacity/default-overlay criterion. -/
theorem ProgressiveList.ssz_try_from_iter_success_represents_iff {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) :
    (∃ self, ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (.Ok self) ∧ self.Represents ValueInst mapInst self.tree.elements) ↔
      ∃ values, IntoIteratorYields iterInst input values ∧ ProgressiveTree.LengthFits factor values.length ∧
        ∃ updates, mapInst.coredefaultDefaultInst.default = ok updates ∧
          (∃ largest, mapInst.max_index updates = ok largest ∧
            largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length) ∧
          ProgressiveListIter.Overlay mapInst updates values values :=
  ProgressiveList.try_from_iter_success_represents_iff ValueInst mapInst iterInst input hlayout

end milhouse.progressive_list
