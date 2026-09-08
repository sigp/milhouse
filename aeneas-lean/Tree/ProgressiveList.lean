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
  simp [ProgressiveList.get, hget, ProgressiveList.backing_get,
    ProgressiveList.backing_len, utils.Length.as_usize, hindex,
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

end milhouse.progressive_list
