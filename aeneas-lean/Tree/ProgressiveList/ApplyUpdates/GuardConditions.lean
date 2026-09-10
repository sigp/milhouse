import Tree.ProgressiveList.ApplyUpdates.Total
import Tree.ProgressiveList.ApplyUpdates.Guards
import Tree.ProgressiveList.ApplyUpdates.QueryTermination

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- With the remaining input, occupied-capacity, and clone-termination laws,
nonempty application succeeds exactly when its reached range queries terminate,
its selected missing-update guards pass, and default construction succeeds.
No range correctness, assumed guard success, or upfront default outcome is
required. This criterion concerns execution, not final backing validity. -/
theorem ProgressiveList.apply_updates_nonempty_success_iff_guards {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val)
    (hfits : ProgressiveTree.LengthFits factor contents.length)
    (hempty : mapInst.is_empty self.updates = ok false) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) ↔
      (∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkRangeOn
          (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
          ValueInst mapInst self.updates factor maximum 0#u32 ∧
        self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32) ∧
      ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults := by
  constructor
  · rintro ⟨result, happly⟩
    have hguards := ProgressiveList.apply_updates_nonempty_guards_pass
      ValueInst mapInst self hlayout hdense.shape hempty happly
    have hqueries := ProgressiveList.apply_updates_nonempty_queries_terminate
      ValueInst mapInst self hlayout hempty happly
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨htrue, _⟩ | ⟨defaults, length, newTree, _, hdefault, _, _, _⟩
    · rw [hempty] at htrue
      cases htrue
    · exact ⟨fun maximum hmax => ⟨hqueries maximum hmax, hguards maximum hmax⟩, defaults, hdefault⟩
  · rintro ⟨hconditions, defaults, hdefault⟩
    obtain ⟨result, happly, _, _⟩ := ProgressiveList.apply_updates_nonempty_success_of_guards
      ValueInst mapInst self contents hlayout hclone
      (fun maximum hmax => (hconditions maximum hmax).1)
      (fun maximum hmax => (hconditions maximum hmax).2)
      hrep hdense hfits hempty defaults hdefault
    exact ⟨result, happly⟩

/-- Both execution branches without range correctness or upfront query,
guard, or default-success laws. The empty-map no-op needs no rebuilding
conditions; input, capacity, and clone-termination laws are conditional on
the nonempty branch. -/
theorem ProgressiveList.apply_updates_success_iff_guards {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hrep : mapInst.is_empty self.updates = ok false → self.Represents ValueInst mapInst contents)
    (hdense : mapInst.is_empty self.updates = ok false → self.tree.Dense factor 0 self.length.val)
    (hlayout : mapInst.is_empty self.updates = ok false → tree.PackingLayout ValueInst factor packingDepth)
    (hfits : mapInst.is_empty self.updates = ok false → ProgressiveTree.LengthFits factor contents.length)
    (hclone : mapInst.is_empty self.updates = ok false →
      ∀ maximum, mapInst.max_index self.updates = ok maximum →
        self.tree.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
          ValueInst mapInst self.updates factor maximum 0#u32) :
    (∃ result, ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) ↔
      mapInst.is_empty self.updates = ok true ∨
      (mapInst.is_empty self.updates = ok false ∧
        (∀ maximum, mapInst.max_index self.updates = ok maximum →
          self.tree.BulkRangeOn
            (fun lo hi => ∃ answer, mapInst.has_any_in_range self.updates lo hi = ok answer)
            ValueInst mapInst self.updates factor maximum 0#u32 ∧
          self.tree.BulkLayerGuardsPass ValueInst mapInst self.updates factor maximum 0#u32) ∧
        ∃ defaults, mapInst.coredefaultDefaultInst.default = ok defaults) := by
  constructor
  · rintro ⟨result, happly⟩
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨hempty, _⟩ | ⟨defaults, length, newTree, hempty, _⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨hempty, (ProgressiveList.apply_updates_nonempty_success_iff_guards
        ValueInst mapInst self contents (hlayout hempty) (hclone hempty)
        (hrep hempty) (hdense hempty) (hfits hempty) hempty).mp ⟨result, happly⟩⟩
  · rintro (hempty | ⟨hempty, hconditions⟩)
    · exact ⟨self, ProgressiveList.apply_updates_empty ValueInst mapInst self hempty⟩
    · exact (ProgressiveList.apply_updates_nonempty_success_iff_guards
        ValueInst mapInst self contents (hlayout hempty) (hclone hempty)
        (hrep hempty) (hdense hempty) (hfits hempty) hempty).mpr hconditions

end milhouse.progressive_list
