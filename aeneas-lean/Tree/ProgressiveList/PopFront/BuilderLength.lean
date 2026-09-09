import Tree.ProgressiveList.PopFront.Builder

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful streaming reconstruction counts every yielded element exactly
once, even when its clone changes its value. Actual execution supplies every
clone and push success; no clone law or builder invariant is needed to derive
the recorded length. -/
theorem ProgressiveListIter.extend_builder_length {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (initial : ProgressiveTreeBuilder T)
    (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) self values)
    {result : ProgressiveTreeBuilder T}
    (hextend : ProgressiveListIter.extend_builder ValueInst mapInst self initial =
      ok (core.result.Result.Ok (), result)) :
    result.length.val = initial.length.val + values.length := by
  obtain ⟨_, _, _, hlength⟩ := ProgressiveListIter.extend_builder_clones
    ValueInst mapInst self initial values hyields hextend
  exact hlength

end milhouse.progressive_list
