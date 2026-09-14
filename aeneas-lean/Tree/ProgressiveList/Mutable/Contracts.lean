import Tree.ProgressiveList.WriteBack
import Tree.UpdateMap.Mutable

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The map read law at the actual closure and environment passed by
`get_mut`. This imposes no behavior at any other fallback invocation. -/
abbrev ProgressiveList.GetMutReads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  update_map.GetMutWithReadsAt mapInst self.updates index
    (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption ValueInst mapInst)
    (self.tree, self.length)

/-- Lookup agreement after writes through handles from this actual map
invocation, using the list's unchanged backing fallback. -/
abbrev ProgressiveList.GetMutWriteReads {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  update_map.GetMutWithWriteReadsAt mapInst self.updates index
    (ProgressiveList.backing_get ValueInst mapInst self)
    (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption ValueInst mapInst)
    (self.tree, self.length)

/-- Maximum-query agreement after writes through this actual map invocation.
Different raw maxima may describe the same logical extent. -/
abbrev ProgressiveList.GetMutMaxIndexAgrees {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  update_map.GetMutWithMaxIndexAgreesAt mapInst self.updates index self.length
    (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption ValueInst mapInst)
    (self.tree, self.length)

/-- A missing handle from this actual map invocation restores the input map.
There is no borrowed element on that branch to which a write law would apply. -/
abbrev ProgressiveList.GetMutMissing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) : Prop :=
  update_map.GetMutWithMissingAt mapInst self.updates index
    (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption ValueInst mapInst)
    (self.tree, self.length)

end milhouse.progressive_list
