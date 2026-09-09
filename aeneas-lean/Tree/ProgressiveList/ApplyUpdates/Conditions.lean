import Tree.ProgressiveList.ApplyUpdates.MaterializedConditions

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Under selected clone/range laws and skipped-value agreement, nonempty
application succeeds and preserves the sequence exactly when final occupied
capacity fits and an actual default outcome preserves the sequence by overlay
and extent. Rebuilding execution is derived, not assumed. -/
theorem ProgressiveList.apply_updates_nonempty_success_represents_iff_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hskipped : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents := by
  have hcriterion := ProgressiveList.apply_updates_nonempty_success_materializes_represents_iff
    ValueInst mapInst self contents hlayout hclone hqueries hrange hrep hbacking hempty
  constructor
  · rintro ⟨result, happly, hresult⟩
    have helements := ProgressiveList.apply_updates_nonempty_backing_contents_of_skipped ValueInst mapInst self contents
      hlayout (fun maximum hmax => (hclone maximum hmax).preserves) hrange hskipped hrep hbacking hempty happly
    obtain ⟨hfits, _, hdefault⟩ := hcriterion.mp ⟨result, happly, helements, hresult⟩
    exact ⟨hfits, hdefault⟩
  · rintro ⟨hfits, hdefault⟩
    obtain ⟨result, happly, _, hresult⟩ := hcriterion.mpr ⟨hfits, hskipped, hdefault⟩
    exact ⟨result, happly, hresult⟩

/-- Under the selected clone and metadata laws, successful nonempty
application preserves the merged sequence exactly when the occupied final
layers fit and the actual default map preserves that sequence by overlay and
extent. Default success and pending emptiness are not assumed as premises;
all rebuilding calls are derived in the reverse direction. -/
theorem ProgressiveList.apply_updates_nonempty_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents) ↔
      ProgressiveTree.LengthFits factor contents.length ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
          (∃ largest, mapInst.max_index defaults = ok largest ∧
            largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
          ProgressiveListIter.Overlay mapInst defaults contents contents := by
  exact ProgressiveList.apply_updates_nonempty_success_represents_iff_of_skipped ValueInst mapInst self contents
    hlayout hclone hqueries hrange
    (fun maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum maximum hmax) self.tree 0#u32)
    hrep hbacking hempty

/-- The public success and sequence criterion uses skipped-value agreement
only on nonempty application. The actual empty no-op is always sufficient;
otherwise occupied capacity and an actual default overlay/extent are necessary
and sufficient under the stated selected clone/range and backing laws. -/
theorem ProgressiveList.apply_updates_success_represents_iff_of_skipped {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hskipped : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkSkippedValuesAgree ValueInst mapInst self.updates maximum contents.length 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents) ↔
      mapInst.is_empty self.updates = ok true ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
            (∃ largest, mapInst.max_index defaults = ok largest ∧
              largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
            ProgressiveListIter.Overlay mapInst defaults contents contents) := by
  constructor
  · rintro ⟨result, happly, hresult⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, _⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨hempty,
        (ProgressiveList.apply_updates_nonempty_success_represents_iff_of_skipped ValueInst mapInst self contents
          (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty) (hskipped hempty)
          hrep (hbacking hempty) hempty).mp ⟨result, happly, hresult⟩⟩
  · rintro (hempty | ⟨hempty, hinputs⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty, hrep⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_represents_iff_of_skipped ValueInst mapInst self contents
        (hlayout hempty) (hclone hempty) (hqueries hempty) (hrange hempty) (hskipped hempty)
        hrep (hbacking hempty) hempty).mpr hinputs

/-- The complete public success and representation criterion distinguishes
the actual empty-map no-op from rebuilding. Every packing, backing, clone, and
range/maximum premise is conditional on the nonempty answer; that branch also
needs precisely final capacity and an actual default-map overlay/extent.
No branch-answer success, default success, or pending-emptiness law is assumed. -/
theorem ProgressiveList.apply_updates_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneLaws ValueInst mapInst self.updates factor maximum 0#u32)
    (hqueries : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
          ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        update_map.MaximumBoundsValues mapInst self.updates maximum) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents) ↔
      mapInst.is_empty self.updates = ok true ∨
        (mapInst.is_empty self.updates = ok false ∧ ProgressiveTree.LengthFits factor contents.length ∧
          ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults ∧
            (∃ largest, mapInst.max_index defaults = ok largest ∧
              largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
            ProgressiveListIter.Overlay mapInst defaults contents contents) := by
  exact ProgressiveList.apply_updates_success_represents_iff_of_skipped ValueInst mapInst self contents
    hrep hbacking hlayout hclone hqueries hrange
    (fun hempty maximum hmax => progressive_tree.ProgressiveTree.BulkSkippedValuesAgree.of_maximum
      contents.length (hmaximum hempty maximum hmax) self.tree 0#u32)

end milhouse.progressive_list
