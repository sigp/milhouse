import Tree.ProgressiveTree

open Aeneas Aeneas.Std Result
open milhouse

set_option maxHeartbeats 2000000

namespace milhouse.progressive_list

/-- A pending update takes precedence over the backing tree, without any
    validity or bounds assumptions on the list. -/
theorem ProgressiveList.get_of_pending_update {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (value : T)
    (hget : mapInst.get self.updates index = ok (some value)) :
    ProgressiveList.get ValueInst mapInst self index = ok (some value) := by
  simp [ProgressiveList.get, hget]

/-- Without a pending update, a read within the backing length is exactly
    the corresponding progressive-tree read. -/
theorem ProgressiveList.get_of_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hget : mapInst.get self.updates index = ok none)
    (hindex : index < self.length) :
    ProgressiveList.get ValueInst mapInst self index =
      progressive_tree.ProgressiveTree.get_recursive ValueInst self.tree index 0#u32 := by
  simp only [ProgressiveList.get, hget, bind_tc_ok, ProgressiveList.backing_get,
    ProgressiveList.backing_len, utils.Length.as_usize, if_pos hindex,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]

/-- The binary-tree density theorem, through the progressive spine, ensures
    that a backing-list read finds a value. Pending updates need only be absent
    at this index; unrelated updates and subtrees impose no assumptions. -/
theorem ProgressiveList.get_some_of_dense_locate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {binary : tree.Tree T} {local_index depth packing_depth : Std.Usize}
    {packing_factor : Option Std.Usize} {len : Nat}
    (hget : mapInst.get self.updates index = ok none)
    (hindex : index < self.length)
    (hlocate : self.tree.locate ValueInst index 0#u32 =
      ok (some (binary, local_index, depth)))
    (hlayout : tree.PackingLayout ValueInst packing_factor packing_depth)
    (hdense : tree.DenseTree packing_factor binary depth.val len)
    (hbits : depth.val + packing_depth.val ≤ System.Platform.numBits)
    (hlocal : local_index.val < len) :
    ∃ value, ProgressiveList.get ValueInst mapInst self index = ok (some value) := by
  rw [ProgressiveList.get_of_backing ValueInst mapInst self index hget hindex]
  exact progressive_tree.ProgressiveTree.get_recursive_some_of_dense_locate
    ValueInst hlocate hlayout hdense hbits hlocal

/-- Binary leaf updates can be read back through both the progressive spine
    and the high-level list API, when not masked by a pending update. -/
theorem ProgressiveList.get_of_located_update {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {before binary : tree.Tree T} {local_index depth packing_depth : Std.Usize}
    {packing_factor : Option Std.Usize} {len : Nat} {value : T}
    (hget : mapInst.get self.updates index = ok none)
    (hindex : index < self.length)
    (hlocate : self.tree.locate ValueInst index 0#u32 =
      ok (some (binary, local_index, depth)))
    (hlayout : tree.PackingLayout ValueInst packing_factor packing_depth)
    (hdense : tree.DenseTree packing_factor before depth.val len)
    (hlocal : local_index.val ≤ len)
    (hupdate : tree.Tree.with_updated_leaf ValueInst before local_index value depth =
      ok (core.result.Result.Ok binary)) :
    ProgressiveList.get ValueInst mapInst self index = ok (some value) := by
  rw [ProgressiveList.get_of_backing ValueInst mapInst self index hget hindex]
  exact progressive_tree.ProgressiveTree.get_recursive_of_located_update
    ValueInst hlocate hlayout hdense hlocal hupdate

/-- A successful push changes only the update map, by inserting at the old
    logical length. Success already rules out a full list and arithmetic
    failure, so callers do not need separate capacity assumptions. -/
theorem ProgressiveList.push_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) (index : Std.Usize)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok index)
    {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    ∃ previous updates, mapInst.insert self.updates index value =
      ok (previous, updates) ∧ pushed = { self with updates := updates } := by
  unfold ProgressiveList.push at hpush
  rw [hlen] at hpush
  simp only [bind_tc_ok] at hpush
  by_cases hfull : index = core.num.Usize.MAX
  · simp [hfull] at hpush
  · rw [if_neg hfull] at hpush
    cases hins : mapInst.insert self.updates index value with
    | fail e => simp [hins] at hpush
    | div => simp [hins] at hpush
    | ok inserted =>
      obtain ⟨previous, updates⟩ := inserted
      simp [hins] at hpush
      exact ⟨previous, updates, rfl, hpush.symm⟩

end milhouse.progressive_list
