import Tree.BulkUpdate.QueryTermination
import Tree.ProgressiveTree.BulkUpdate.LayerRangeScope
import Tree.ProgressiveTree.BulkUpdate.Visited

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Actual successful traversal certifies termination of every reached
progressive range query. Empty windows do not query the external map. No
packing, input-invariant, map-correctness, or clone law is assumed. -/
theorem ProgressiveTree.with_updated_leaves_recursive_layer_queries_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    before.BulkLayerRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      ValueInst mapInst updates maximum depth := by
  intro start stop hquery
  induction hquery generalizing after with
  | @here before depth next start stop binary hgeometry hnonempty =>
    have unwrap : ∀ answer,
        ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok answer →
        mapInst.has_any_in_range updates start stop = ok answer := by
      intro answer hhas
      simpa only [ProgressiveTree.has_updates_in_range,
        if_pos ((UScalar.lt_equiv _ _).mpr hnonempty)] using hhas
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | zero hempty => exact ⟨false, unwrap false hempty⟩
    | expand _ hhas _ _ => exact ⟨true, unwrap true hhas⟩
    | node _ _ hleft _ =>
      rcases hleft with ⟨hempty, _⟩ | ⟨hhas, _⟩
      · exact ⟨false, unwrap false hempty⟩
      · exact ⟨true, unwrap true hhas⟩
  | zero_tail hgeometry hhas hselected _ ih =>
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | zero hempty => rw [hhas] at hempty; cases hempty
    | expand _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive
  | node_tail hgeometry _ hselected _ ih =>
    have hstep := hgeometry.step_of_update hupdate
    cases hstep with
    | node _ _ _ hright =>
      rcases hright with ⟨hbefore, _⟩ | ⟨_, hrecursive⟩
      · obtain ⟨last, hlast, hbound⟩ := hselected
        have := hbefore last hlast
        omega
      · exact ih hrecursive

/-- Successful progressive rebuilding supplies termination of the complete
query scope, including selected binary queries. Layout is the only semantic
law: no shape, density, clone, lookup, or range correctness is assumed. -/
theorem ProgressiveTree.with_updated_leaves_recursive_queries_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {before after : ProgressiveTree T} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (.Ok after)) :
    before.BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      ValueInst mapInst updates factor maximum depth := by
  refine (ProgressiveTree.BulkRangeOn.iff_layers_binary
    (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
    ValueInst mapInst updates factor maximum before depth).mpr ?_
  refine ⟨ProgressiveTree.with_updated_leaves_recursive_layer_queries_terminate
    ValueInst mapInst updates hupdate, ?_⟩
  intro layer start binary hvisit
  obtain ⟨result, hresult⟩ := hvisit.update_success hupdate
  simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
    tree.Tree.with_updated_leaves_queries_terminate ValueInst mapInst hlayout (by simp) hresult

/-- Successful public rebuilding certifies all scoped query termination for
its actual maximum answer, with no external termination premise. -/
theorem ProgressiveTree.with_updated_leaves_queries_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {before after : ProgressiveTree T}
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after)) :
    ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkRangeOn
        (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
        ValueInst mapInst updates factor maximum 0#u32 := by
  intro maximum hmax
  unfold ProgressiveTree.with_updated_leaves at hupdate
  simp only [hmax, bind_tc_ok] at hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_queries_terminate ValueInst mapInst updates hlayout hupdate

end milhouse.progressive_tree
