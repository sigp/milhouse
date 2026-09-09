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

/-- Successful vector cloning preserves one optional lookup if the element
at that position clones identically. Other element results may differ, and a
missing position needs no clone law. -/
theorem vec_clone_get_of_clone_at {T : Type} (cloneInst : core.clone.Clone T)
    {self copied : alloc.vec.Vec T} (index : Nat)
    (hclone : alloc.vec.CloneVec.clone cloneInst self = ok copied)
    (hidentity : ∀ value, self.val[index]? = some value → cloneInst.clone value = ok value) :
    copied.val[index]? = self.val[index]? := by
  have hmap := vec_clone_mapM cloneInst hclone
  have hlength := List.mapM_Result_length hmap
  by_cases hin : index < self.val.length
  · have hcopy : index < copied.val.length := by omega
    have hactual := List.mapM_Result_ok hmap index hin
    have hvalue := Result.ok.inj
      (hactual.symm.trans (hidentity self.val[index] (by simp [hin])))
    simp only [_root_.List.getElem?_eq_getElem hin,
      _root_.List.getElem?_eq_getElem hcopy, hvalue]
  · rw [_root_.List.getElem?_eq_none (by omega), _root_.List.getElem?_eq_none (by omega)]

end milhouse_models
