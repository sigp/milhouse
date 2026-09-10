import Tree.BulkUpdate.SkippedContents
import Tree.ProgressiveTree.BulkUpdate.RetainedClones
import Tree.ProgressiveTree.BulkUpdate.LayerRangeScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Pending values skipped inside selected binary layers agree with their
original slots. Progressive layer selection and binary query scope both use
actual input observations, without an assumed rebuilding result. -/
def ProgressiveTree.BulkBinarySkippedValuesAgree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor maximum : Option Std.Usize) (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    layer.BulkSkippedValuesAgree mapInst updates factor binary.val 0 start.val

/-- Exclusion in all selected binary ranges supplies skipped-slot agreement. -/
theorem ProgressiveTree.BulkBinarySkippedValuesAgree.of_ranges {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (hrange : self.BulkBinaryRangeOn (update_map.RangeExcludesValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth) :
    self.BulkBinarySkippedValuesAgree ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact tree.Tree.BulkSkippedValuesAgree.of_ranges layer binary.val 0 start.val
    (by simpa only [Nat.zero_add] using hrange layer start binary hvisit)

/-- Correct mathematical slots after successful progressive rebuilding force
agreement in every skipped window of its selected binary layers. Layout alone
identifies the windows; no input shape, density, capacity, range, clone, or
termination law is assumed. -/
theorem ProgressiveTree.with_updated_leaves_recursive_binary_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after))
    (hcontents : ProgressiveTree.BulkSlotContents mapInst updates factor before after depth.val) :
    before.BulkBinarySkippedValuesAgree ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  obtain ⟨result, hresult, hbinaryContents⟩ := hvisit.update_success_contents hlayout hupdate hcontents
  exact tree.Tree.with_updated_leaves_skipped_values_agree ValueInst mapInst hlayout
    (by simp) hresult hbinaryContents

/-- The public progressive wrapper supplies binary skipped-slot agreement
for its actual maximum answer whenever its final mathematical slots are correct. -/
theorem ProgressiveTree.with_updated_leaves_binary_skipped_values_agree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after))
    (hcontents : ProgressiveTree.BulkSlotContents mapInst updates factor before after 0) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkBinarySkippedValuesAgree ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_binary_skipped_values_agree
    ValueInst mapInst updates hlayout hupdate hcontents

end milhouse.progressive_tree
