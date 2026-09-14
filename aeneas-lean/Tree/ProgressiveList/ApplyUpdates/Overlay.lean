import Tree.ProgressiveList.ApplyUpdates.Backing
import Tree.ProgressiveList.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The actual rebuilt-value overlay and installed-map extent characterize
representation using only numeric layer range conditions and selected binary
reflection. Clone identity and skipped-value agreement are unnecessary because
the criterion observes the actual rebuilt values. -/
theorem ProgressiveList.apply_updates_nonempty_represents_iff_of_range_extents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hlayers : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn
        (update_map.RangePreservesExtentAt mapInst self.updates self.length.val contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.Represents ValueInst mapInst contents ↔
      (∃ largest, mapInst.max_index result.updates = ok largest ∧
        largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
      ProgressiveListIter.Overlay mapInst result.updates result.tree.elements contents := by
  have hafter := ProgressiveList.apply_updates_preserves_backing_of_range_extents ValueInst mapInst self contents
    (fun _ => hlayout) (fun _ => hlayers) (fun _ => hrange) hrep hbacking happly
  have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
    ValueInst mapInst self contents hrep hempty happly
  simpa only [hlength] using ProgressiveList.represents_iff_overlay_of_length
    ValueInst mapInst hlayout result contents hafter.1 hafter.2 hlength

/-- Successful nonempty application represents the original merged sequence
exactly when the installed map overlays the actual rebuilt values to that
sequence and preserves its logical extent. Clone identity and empty-default
laws are not separately assumed; successful execution supplies the new length
and traversal bounds under the stated range and backing invariants. -/
theorem ProgressiveList.apply_updates_nonempty_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.Represents ValueInst mapInst contents ↔
      (∃ largest, mapInst.max_index result.updates = ok largest ∧
        largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
      ProgressiveListIter.Overlay mapInst result.updates result.tree.elements contents := by
  exact ProgressiveList.apply_updates_nonempty_represents_iff_of_range_extents ValueInst mapInst self contents
    hlayout
    (fun maximum hmax => (hrange maximum hmax).layers
      (fun _ _ h => h.preservesExtent hrep.dense_update_domain))
    (fun maximum hmax => (hrange maximum hmax).binary_layers)
    hrep hbacking hempty happly

/-- Complete representation uses numeric layer range conditions only on
nonempty application, together with reflection inside selected binary subtrees.
The no-op preserves representation directly; the rebuilt branch has the exact
actual-value overlay and installed-map extent criterion. -/
theorem ProgressiveList.apply_updates_represents_iff_of_range_extents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hlayers : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkLayerRangeOn
        (update_map.RangePreservesExtentAt mapInst self.updates self.length.val contents.length)
        ValueInst mapInst self.updates maximum 0#u32)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.Represents ValueInst mapInst contents ↔
      (mapInst.is_empty self.updates = ok false →
        (∃ largest, mapInst.max_index result.updates = ok largest ∧
          largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
        ProgressiveListIter.Overlay mapInst result.updates result.tree.elements contents) := by
  constructor
  · intro hresult hempty
    exact (ProgressiveList.apply_updates_nonempty_represents_iff_of_range_extents ValueInst mapInst self contents
      (hlayout hempty) (hlayers hempty) (hrange hempty) hrep (hbacking hempty) hempty happly).mp hresult
  · intro hmap
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨_, rfl⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact hrep
    · exact (ProgressiveList.apply_updates_nonempty_represents_iff_of_range_extents ValueInst mapInst self contents
        (hlayout hempty) (hlayers hempty) (hrange hempty) hrep (hbacking hempty) hempty happly).mpr
        (hmap hempty)

/-- For the complete public operation, exact rebuilt-value overlay and
extent laws are needed only on the actual nonempty branch. An empty-map
no-op preserves representation without packing, backing, range, clone, or
default-map premises. No pending-emptiness law is needed by this criterion. -/
theorem ProgressiveList.apply_updates_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : mapInst.is_empty self.updates = ok false →
      tree.PackingLayout ValueInst factor packingDepth)
    (hrange : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : mapInst.is_empty self.updates = ok false → self.BackingValid factor)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.Represents ValueInst mapInst contents ↔
      (mapInst.is_empty self.updates = ok false →
        (∃ largest, mapInst.max_index result.updates = ok largest ∧
          largest.elim contents.length (fun index => max (index.val + 1) contents.length) = contents.length) ∧
        ProgressiveListIter.Overlay mapInst result.updates result.tree.elements contents) := by
  exact ProgressiveList.apply_updates_represents_iff_of_range_extents ValueInst mapInst self contents
    hlayout
    (fun hempty maximum hmax => (hrange hempty maximum hmax).layers
      (fun _ _ h => h.preservesExtent hrep.dense_update_domain))
    (fun hempty maximum hmax => (hrange hempty maximum hmax).binary_layers)
    hrep hbacking happly

end milhouse.progressive_list
