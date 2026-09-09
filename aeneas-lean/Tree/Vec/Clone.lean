import Tree.Funs

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- A successful vector clone stores the actual element-clone results in
order. No identity or termination law is assumed; success supplies the trace. -/
theorem vec_clone_mapM {T : Type} (cloneInst : core.clone.Clone T)
    {self copied : alloc.vec.Vec T}
    (hclone : alloc.vec.CloneVec.clone cloneInst self = ok copied) :
    _root_.List.mapM cloneInst.clone self.val = ok copied.val := by
  unfold alloc.vec.CloneVec.clone Slice.clone Aeneas.Std.List.clone at hclone
  split at hclone <;> simp_all
  exact congrArg (fun value : alloc.vec.Vec T => value.val) (Result.ok.inj hclone)

end milhouse_models
