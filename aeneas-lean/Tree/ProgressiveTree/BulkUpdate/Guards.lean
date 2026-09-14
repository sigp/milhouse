import Tree.BulkUpdate.GuardsNecessary
import Tree.ProgressiveTree.BulkUpdate.Activation
import Tree.ProgressiveTree.BulkUpdate.Visited

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Actual missing-update guards pass in every selected binary layer. The
scope uses input geometry and range/maximum answers, with no rebuilding result. -/
def ProgressiveTree.BulkLayerGuardsPass {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor maximum : Option Std.Usize) (self : ProgressiveTree T) (depth : Std.U32) : Prop :=
  ∀ layer start binary,
    self.BulkLayerVisited ValueInst mapInst updates maximum depth layer start binary →
    tree.BulkGuardsPass mapInst updates factor binary.val start.val

/-- The previous activation and selected binary reflection laws supply the
weaker actual guard condition. Range-query termination is not required. -/
theorem ProgressiveTree.BulkLayerGuardsPass.of_enabled {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {self : ProgressiveTree T} {depth : Std.U32}
    (henabled : self.BulkLayerEnabled ValueInst mapInst updates factor maximum depth)
    (hrange : self.BulkBinaryRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth) :
    self.BulkLayerGuardsPass ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  exact tree.BulkGuardsPass.of_enabled (henabled layer start binary hvisit) (hrange layer start binary hvisit)

theorem ProgressiveTree.BulkLayerGuardsPass.zero_left {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerGuardsPass
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkGuardsPass mapInst updates factor binary.val start.val :=
  hself _ _ _ (.zero_here hgeometry hhas)

theorem ProgressiveTree.BulkLayerGuardsPass.node_left {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerGuardsPass
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true) :
    tree.BulkGuardsPass mapInst updates factor binary.val start.val :=
  hself _ _ _ (.node_here hgeometry hhas)

theorem ProgressiveTree.BulkLayerGuardsPass.zero_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    (hself : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerGuardsPass
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    (ProgressiveTree.ProgressiveZero : ProgressiveTree T).BulkLayerGuardsPass
      ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  exact hself _ _ _ (.zero_tail hgeometry hhas hmaximum hvisit)

theorem ProgressiveTree.BulkLayerGuardsPass.node_right {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {factor maximum : Option Std.Usize} {depth next : Std.U32} {start stop binary : Std.Usize}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)} {left : tree.Tree T} {right : ProgressiveTree T}
    (hself : (ProgressiveTree.ProgressiveNode hash left right).BulkLayerGuardsPass
      ValueInst mapInst updates factor maximum depth)
    (hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary)
    (hhas : ∃ has, ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has)
    (hmaximum : ∃ last, maximum = some last ∧ stop.val ≤ last.val) :
    right.BulkLayerGuardsPass ValueInst mapInst updates factor maximum next := by
  intro layer layerStart layerDepth hvisit
  obtain ⟨has, hhas⟩ := hhas
  exact hself _ _ _ (.node_tail hgeometry hhas hmaximum hvisit)


/-- Successful progressive rebuilding certifies all selected binary guards.
Layout and input shape suffice; no range, clone, termination, density, or
capacity law is assumed. -/
theorem ProgressiveTree.with_updated_leaves_recursive_guards_pass {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hshape : before.Shape factor depth.val)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    before.BulkLayerGuardsPass ValueInst mapInst updates factor maximum depth := by
  intro layer start binary hvisit
  obtain ⟨result, hresult⟩ := hvisit.update_success hupdate
  simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
    tree.Tree.with_updated_leaves_guards_pass ValueInst mapInst hlayout (hvisit.shape hshape) (by simp) hresult

/-- The public progressive wrapper supplies the selected binary guard condition
for its actual maximum answer. -/
theorem ProgressiveTree.with_updated_leaves_guards_pass {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T}
    (hshape : before.Shape factor 0)
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after)) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkLayerGuardsPass ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_guards_pass ValueInst mapInst updates hlayout hshape hupdate

end milhouse.progressive_tree
