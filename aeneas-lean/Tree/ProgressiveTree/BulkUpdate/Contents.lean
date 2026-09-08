import Tree.ProgressiveTree.BulkUpdate.Layer
import Tree.ProgressiveTree.BulkUpdate.Range
import Tree.ProgressiveTree.BulkUpdate.Steps

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Contents of a successfully updated suffix, at every query in the new
    logical prefix. Pending values override the previous extracted lookup. -/
def ProgressiveTree.BulkContents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (before after : ProgressiveTree T)
    (depth : Std.U32) (newLength : Std.Usize) : Prop :=
  ∀ (query : Std.Usize) (pending : Option T),
    progressiveCapacity factor depth.val ≤ query.val → query.val < newLength.val →
    mapInst.get updates query = ok pending →
    ProgressiveTree.get_recursive ValueInst after query depth =
      match pending with
      | some value => ok (some value)
      | none => ProgressiveTree.get_recursive ValueInst before query depth

private theorem zero_get {T : Type} (ValueInst : Value T) (query : Std.Usize) (depth : Std.U32) :
    ProgressiveTree.get_recursive ValueInst .ProgressiveZero query depth = ok none := by
  rw [ProgressiveTree.get_recursive]

private theorem node_get_right {T : Type} (ValueInst : Value T)
    {left : tree.Tree T} {right : ProgressiveTree T}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {depth next : Std.U32} {stop query : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hroute : ¬ query < stop) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode hash left right) query depth =
      ProgressiveTree.get_recursive ValueInst right query next := by
  rw [ProgressiveTree.get_recursive]
  simp only [hnext, hstop, bind_tc_ok, if_neg hroute, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]

private theorem node_get_same_left {T : Type} (ValueInst : Value T)
    {left : tree.Tree T} {oldRight newRight : ProgressiveTree T}
    {oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {depth next : Std.U32} {stop query : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hroute : query < stop) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode newHash left newRight) query depth =
      ProgressiveTree.get_recursive ValueInst (.ProgressiveNode oldHash left oldRight) query depth := by
  rw [ProgressiveTree.get_recursive, ProgressiveTree.get_recursive]
  simp only [hnext, hstop, bind_tc_ok, if_pos hroute]

private theorem bulk_contents_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {maximum : Option Std.Usize} (hmaximum : update_map.MaximumBoundsValues mapInst updates maximum)
    {oldLength : Nat} {newLength : Std.Usize}
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength.val) :
    ∀ (fuel : Nat) (depth : Std.U32) (before after : ProgressiveTree T),
      Std.U32.max - depth.val ≤ fuel →
      before.Shape factor depth.val → before.EndsAfter factor depth.val oldLength →
      ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
        ok (core.result.Result.Ok after) →
      after.Shape factor depth.val ∧ after.EndsAfter factor depth.val newLength.val ∧
        ProgressiveTree.BulkContents ValueInst mapInst updates factor before after depth newLength := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro depth before after hfuel hshape hends hupdate
    obtain ⟨start, next, stop, binary, hstart, hnext, hstop, hbinary, hstep⟩ :=
      ProgressiveTree.with_updated_leaves_recursive_step ValueInst mapInst hupdate
    have hadd := UScalar.add_equiv depth 1#u32
    rw [hnext] at hadd
    simp at hadd
    have hnextVal : next.val = depth.val + 1 := by omega
    have hless : Std.U32.max - next.val < fuel := by scalar_tac
    obtain ⟨actualStart, hactualStart, hstartVal⟩ :=
      ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
    rw [hstart] at hactualStart
    cases hactualStart
    have hstartLe : start.val ≤ progressiveCapacity factor depth.val := by omega
    obtain ⟨actualStop, hactualStop, hstopVal⟩ :=
      ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq next
    rw [hstop] at hactualStop
    cases hactualStop
    have hstopLe : stop.val ≤ progressiveCapacity factor next.val := by omega
    have rightCorrect : ∀ (right newRight : ProgressiveTree T),
        right.Shape factor next.val → right.EndsAfter factor next.val oldLength →
        ProgressiveTree.BulkRightStep ValueInst mapInst updates maximum next stop right newRight →
        newRight.Shape factor next.val ∧ newRight.EndsAfter factor next.val newLength.val ∧
          ProgressiveTree.BulkContents ValueInst mapInst updates factor right newRight next newLength := by
      intro right newRight hrightShape hrightEnds hright
      rcases hright with ⟨hbefore, rfl⟩ | ⟨_, hrecursive⟩
      · have hlength := hcomplete.length_le_max_of_maximum_before hmaximum hbefore
        refine ⟨hrightShape, ?_, ?_⟩
        · by_cases hold : newLength.val ≤ oldLength
          · exact hrightEnds.mono hold
          · exact ProgressiveTree.endsAfter_of_le_start factor _ (by omega)
        · intro query pending hlo hhi hget
          have hnone := update_map.get_none_of_maximum_before mapInst updates hmaximum hbefore
            (by omega) hget
          simp only [hnone]
      · exact ih _ hless next right newRight (Nat.le_refl _) hrightShape hrightEnds hrecursive
    have queryAfterStop : ∀ query : Std.Usize, ¬ query < stop → query.val < newLength.val →
        progressiveCapacity factor next.val ≤ query.val := by
      intro query hroute hhi
      have hstopSmall : stop.val < Std.Usize.max := by scalar_tac
      have hstopQuery : stop.val ≤ query.val := by scalar_tac
      have hstopExact := ProgressiveTree.total_capacity_unclamped ValueInst
        hlayout.opt_packing_factor_eq hstop hstopSmall
      omega
    cases hstep with
    | zero hempty =>
      have hlength := ProgressiveTree.length_le_of_empty_zero_layer ValueInst mapInst
        hlayout hrange hcomplete hnext hstart hstop hends hempty
      refine ⟨.zero factor depth.val, hlength, ?_⟩
      intro query pending hlo hhi hget
      omega
    | @expand right newLeft hash hhas hleft hright =>
      have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
      have hzeroShape : (tree.Tree.Zero binary : tree.Tree T).Shape factor (2 * depth.val) := by
        rw [← hbinaryVal]
        exact .zero factor binary
      have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
      obtain ⟨hleftShape, _, _, _⟩ := ProgressiveTree.updated_layer_contents ValueInst mapInst updates
        hlayout hclone hrange hnext hstart hstop hbinary hnonempty hzeroShape hleft
      have hrightEnds : ProgressiveTree.EndsAfter factor (.ProgressiveZero : ProgressiveTree T)
          next.val oldLength := by
        change oldLength ≤ progressiveCapacity factor next.val
        exact le_trans hends (progressiveCapacity_mono factor (by omega))
      obtain ⟨hrightShape, hrightEnds, hrightContents⟩ :=
        rightCorrect .ProgressiveZero right (.zero factor next.val) hrightEnds hright
      refine ⟨.node hash hleftShape (by simpa only [hnextVal] using hrightShape),
        by simpa only [ProgressiveTree.EndsAfter, hnextVal] using hrightEnds, ?_⟩
      intro query pending hlo hhi hget
      by_cases hroute : query < stop
      · have hread := ProgressiveTree.get_after_expanded_layer ValueInst mapInst updates
          hlayout hclone hrange (hash := hash) (right := right) hnext hstart hstop hbinary
          (by omega) (by scalar_tac) hget hleft
        cases pending <;> simpa only [zero_get] using hread
      · rw [node_get_right ValueInst hnext hstop hroute]
        have hread := hrightContents query pending (queryAfterStop query hroute hhi) hhi hget
        simpa only [zero_get] using hread
    | @node left newLeft right newRight oldHash newHash hleft hright =>
      cases hshape with
      | node _ hleftShape hrightShape =>
        have hrightShape' : right.Shape factor next.val := by simpa only [hnextVal] using hrightShape
        have hrightEnds : right.EndsAfter factor next.val oldLength := by
          simpa only [ProgressiveTree.EndsAfter, hnextVal] using hends
        obtain ⟨hnewRightShape, hnewRightEnds, hrightContents⟩ :=
          rightCorrect right newRight hrightShape' hrightEnds hright
        have hnewLeftShape : newLeft.Shape factor (2 * depth.val) := by
          rcases hleft with ⟨_, rfl⟩ | ⟨hhas, hleft⟩
          · exact hleftShape
          · have hnonempty := (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1
            exact (ProgressiveTree.updated_layer_contents ValueInst mapInst updates hlayout hclone hrange
              hnext hstart hstop hbinary hnonempty hleftShape hleft).1
        refine ⟨.node newHash hnewLeftShape (by simpa only [hnextVal] using hnewRightShape),
          by simpa only [ProgressiveTree.EndsAfter, hnextVal] using hnewRightEnds, ?_⟩
        intro query pending hlo hhi hget
        by_cases hroute : query < stop
        · rcases hleft with ⟨hempty, rfl⟩ | ⟨_, hleft⟩
          · have hnone := ProgressiveTree.has_updates_in_range_false_excludes ValueInst mapInst
              hrange hempty hget (by omega) (by scalar_tac)
            simp only [hnone]
            exact node_get_same_left ValueInst hnext hstop hroute
          · exact ProgressiveTree.get_after_updated_layer_override ValueInst mapInst updates hlayout hclone hrange
              hnext hstart hstop hbinary hleftShape (by omega) (by scalar_tac) hget hleft
        · rw [node_get_right ValueInst hnext hstop hroute, node_get_right ValueInst hnext hstop hroute]
          exact hrightContents query pending (queryAfterStop query hroute hhi) hhi hget

/-- Complete recursive progressive bulk-update correctness. The supplied
    maximum need only bound pending values, and only false range answers need
    exclude them. Contiguous extension values justify the zero early exit.
    No arithmetic-success, shift, or window-alignment premises are added. -/
theorem ProgressiveTree.with_updated_leaves_recursive_shape_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {maximum : Option Std.Usize} (hmaximum : update_map.MaximumBoundsValues mapInst updates maximum)
    {oldLength : Nat} {newLength : Std.Usize}
    (hcomplete : update_map.ExtensionComplete mapInst updates oldLength newLength.val)
    {before after : ProgressiveTree T} {depth : Std.U32}
    (hshape : before.Shape factor depth.val) (hends : before.EndsAfter factor depth.val oldLength)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (core.result.Result.Ok after)) :
    after.Shape factor depth.val ∧ after.EndsAfter factor depth.val newLength.val ∧
      ProgressiveTree.BulkContents ValueInst mapInst updates factor before after depth newLength := by
  exact bulk_contents_aux ValueInst mapInst updates hlayout hclone hrange hmaximum hcomplete
    (Std.U32.max - depth.val) depth before after (Nat.le_refl _) hshape hends hupdate

end milhouse.progressive_tree
