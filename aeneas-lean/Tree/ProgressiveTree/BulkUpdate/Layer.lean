import Tree.ProgressiveTree.Geometry
import Tree.BulkUpdate.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Updating a nonempty progressive layer preserves binary shape and applies
    exactly its pending values. Both alignment and the exact window width are
    derived from extracted capacities and successful update execution. -/
theorem ProgressiveTree.updated_layer_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {depth next : Std.U32} {start stop binary : Std.Usize}
    {before after : tree.Tree T}
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hnonempty : start.val < stop.val)
    (hshape : before.Shape factor (2 * depth.val))
    (hupdate : tree.Tree.with_updated_leaves ValueInst mapInst before updates
      0#usize start binary none = ok (core.result.Result.Ok after)) :
    after.Shape factor (2 * depth.val) ∧
      start.val % tree.leafCapacity factor = 0 ∧
      stop.val = start.val + tree.subtreeCapacity factor binary.val ∧
      tree.Tree.BulkContents mapInst updates factor before after binary.val 0 start.val := by
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hstartVal := ProgressiveTree.total_capacity_unclamped ValueInst
    hlayout.opt_packing_factor_eq hstart (by scalar_tac)
  have hoffset : start.val % tree.leafCapacity factor = 0 := by
    rw [hstartVal]
    exact progressiveCapacity_aligned factor depth.val
  have hshape' : before.Shape factor binary.val := by simpa only [hbinaryVal] using hshape
  obtain ⟨hfit, hafter, hcontents⟩ := tree.Tree.with_updated_leaves_capacity_shape_contents
    ValueInst mapInst updates hlayout
    (tree.Tree.BulkCloneOn.of_all mapInst updates factor hclone before binary.val _)
    hrange hshape' (by simp) hoffset hupdate
  obtain ⟨actualStart, actualStop, hactualStart, hactualStop, _, hwidth, _⟩ :=
    ProgressiveTree.layer_window ValueInst hlayout hnext hbinary hfit
  rw [hstart] at hactualStart
  rw [hstop] at hactualStop
  cases hactualStart
  cases hactualStop
  exact ⟨by simpa only [hbinaryVal] using hafter, hoffset, hwidth, hcontents⟩

private theorem saturating_sub_val (index start : Std.Usize) :
    (core.num.Usize.saturating_sub index start).val = index.val - start.val := by
  change (index.val - start.val) % 2 ^ UScalarTy.Usize.numBits = index.val - start.val
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- Read-back through a progressive node after updating its selected binary
    layer. The query is global; the proof derives the local index, aligned map
    offset, and binary bounds required by the binary read-back theorem. -/
theorem ProgressiveTree.get_after_updated_layer {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {depth next : Std.U32} {start stop binary query : Std.Usize}
    {before after : tree.Tree T} {oldRight newRight : ProgressiveTree T}
    {oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {pending : Option T}
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hshape : before.Shape factor (2 * depth.val))
    (hqueryLo : start.val ≤ query.val) (hqueryHi : query.val < stop.val)
    (hget : mapInst.get updates query = ok pending)
    (hupdate : tree.Tree.with_updated_leaves ValueInst mapInst before updates
      0#usize start binary none = ok (core.result.Result.Ok after)) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode newHash after newRight) query depth =
      (do let previous ← ProgressiveTree.get_recursive ValueInst
            (.ProgressiveNode oldHash before oldRight) query depth
          ok (pending.or previous)) := by
  obtain ⟨_, hoffset, hwidth, _⟩ := ProgressiveTree.updated_layer_contents
    ValueInst mapInst updates hlayout hclone hrange hnext hstart hstop hbinary
    (by omega) hshape hupdate
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hshape' : before.Shape factor binary.val := by simpa only [hbinaryVal] using hshape
  have hlocal := saturating_sub_val query start
  have hread := tree.Tree.get_after_with_updated_leaves ValueInst mapInst updates
    hlayout (tree.Tree.BulkCloneOn.of_all mapInst updates factor hclone before binary.val _)
    hrange hshape' (by simp) hoffset
    (index := core.num.Usize.saturating_sub query start) (by omega)
    (by simp) (by simp only [hlocal]; omega) hget hupdate
  have hroute : query < stop := by scalar_tac
  simpa only [ProgressiveTree.get_recursive, hnext, hstop, hstart, hbinary, if_pos hroute,
    hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using hread

/-- Expanding an empty progressive suffix reads back the pending value in the
    newly created layer. No prior binary contents or sibling invariant is
    assumed; the untouched zero layer supplies `none` directly. -/
theorem ProgressiveTree.get_after_expanded_layer {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {depth next : Std.U32} {start stop binary query : Std.Usize}
    {after : tree.Tree T} {right : ProgressiveTree T}
    {hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {pending : Option T}
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hqueryLo : start.val ≤ query.val) (hqueryHi : query.val < stop.val)
    (hget : mapInst.get updates query = ok pending)
    (hupdate : tree.Tree.with_updated_leaves ValueInst mapInst (.Zero binary) updates
      0#usize start binary none = ok (core.result.Result.Ok after)) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode hash after right) query depth =
      ok pending := by
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hshape : (tree.Tree.Zero binary : tree.Tree T).Shape factor (2 * depth.val) := by
    rw [← hbinaryVal]
    exact .zero factor binary
  have hread := ProgressiveTree.get_after_updated_layer ValueInst mapInst updates
    hlayout hclone hrange (oldHash := hash) (oldRight := .ProgressiveZero)
    (newHash := hash) (newRight := right)
    hnext hstart hstop hbinary hshape hqueryLo hqueryHi hget hupdate
  have hroute : query < stop := by scalar_tac
  simpa only [ProgressiveTree.get_recursive, hnext, hstop, hstart, hbinary, if_pos hroute,
    hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, tree.get_recursive_zero,
    Option.or_none] using hread

/-- A pending value determines the updated read directly. Successful update
    execution certifies that the old selected binary read succeeds, so this
    law needs no separate readability premise. -/
theorem ProgressiveTree.get_after_updated_layer_override {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {depth next : Std.U32} {start stop binary query : Std.Usize}
    {before after : tree.Tree T} {oldRight newRight : ProgressiveTree T}
    {oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {pending : Option T}
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hshape : before.Shape factor (2 * depth.val))
    (hqueryLo : start.val ≤ query.val) (hqueryHi : query.val < stop.val)
    (hget : mapInst.get updates query = ok pending)
    (hupdate : tree.Tree.with_updated_leaves ValueInst mapInst before updates
      0#usize start binary none = ok (core.result.Result.Ok after)) :
    ProgressiveTree.get_recursive ValueInst (.ProgressiveNode newHash after newRight) query depth =
      match pending with
      | some value => ok (some value)
      | none => ProgressiveTree.get_recursive ValueInst (.ProgressiveNode oldHash before oldRight) query depth := by
  obtain ⟨_, _, hwidth, _⟩ := ProgressiveTree.updated_layer_contents ValueInst mapInst updates
    hlayout hclone hrange hnext hstart hstop hbinary (by omega) hshape hupdate
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hshape' : before.Shape factor binary.val := by simpa only [hbinaryVal] using hshape
  have hstopBound : stop.val < 2 ^ System.Platform.numBits := by simpa using stop.hBounds
  have hcapacity : tree.subtreeCapacity factor binary.val < 2 ^ System.Platform.numBits := by omega
  have hbits : binary.val + packingDepth.val ≤ System.Platform.numBits := by
    rw [hlayout.subtreeCapacity_eq_two_pow] at hcapacity
    by_contra hnot
    have hle : System.Platform.numBits ≤ packingDepth.val + binary.val := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega
  have hbeforeRead := hshape'.get_recursive_eq_slot hlayout binary rfl hbits
    (core.num.Usize.saturating_sub query start)
  have hroute : query < stop := by scalar_tac
  have hbefore : ProgressiveTree.get_recursive ValueInst
      (.ProgressiveNode oldHash before oldRight) query depth =
      ok (before.slot factor binary.val (core.num.Usize.saturating_sub query start).val) := by
    simpa only [ProgressiveTree.get_recursive, hnext, hstop, hstart, hbinary, if_pos hroute,
      hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] using hbeforeRead
  have hread := ProgressiveTree.get_after_updated_layer ValueInst mapInst updates hlayout hclone hrange
    (oldHash := oldHash) (newHash := newHash) (oldRight := oldRight) (newRight := newRight)
    hnext hstart hstop hbinary hshape hqueryLo hqueryHi hget hupdate
  cases pending <;> simpa only [hbefore, bind_tc_ok, Option.none_or, Option.some_or] using hread

end milhouse.progressive_tree
