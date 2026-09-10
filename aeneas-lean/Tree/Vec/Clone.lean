import Tree.Funs

open Aeneas Aeneas.Std Result

namespace milhouse_models

/-- Ordered element cloning succeeds exactly when the clone of every input
value terminates. This imposes no identity or coherence law on clone results. -/
theorem list_clone_success_iff {T : Type} (cloneInst : core.clone.Clone T)
    (values : _root_.List T) :
    (∃ copied, _root_.List.mapM cloneInst.clone values = ok copied) ↔
      ∀ value ∈ values, ∃ copied, cloneInst.clone value = ok copied := by
  induction values with
  | nil => simp [_root_.List.mapM_nil, Pure.pure]
  | cons value values ih =>
    simp only [_root_.List.forall_mem_cons, ← ih]
    cases hhead : cloneInst.clone value <;>
      cases htail : _root_.List.mapM cloneInst.clone values <;>
      simp [_root_.List.mapM_cons, hhead, htail, Pure.pure]

/-- Identity is needed only for the actual input values to make their
ordered cloning return the original list. -/
theorem list_clone_identity {T : Type} (cloneInst : core.clone.Clone T)
    (values : _root_.List T)
    (hclone : ∀ value ∈ values, cloneInst.clone value = ok value) :
    _root_.List.mapM cloneInst.clone values = ok values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have hhead := hclone value (by simp)
    have htail := ih (fun item hitem => hclone item (by simp [hitem]))
    simp only [_root_.List.mapM_cons, hhead, htail, bind_tc_ok, Pure.pure]

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

/-- Optional cloning preserves its input exactly when the present value
clones identically. A missing value needs no clone law. -/
theorem option_clone_identity_iff {T : Type} (cloneInst : core.clone.Clone T)
    (value : Option T) :
    core.option.OptionShared0T.cloned cloneInst value = ok value ↔
      ∀ item, value = some item → cloneInst.clone item = ok item := by
  cases value with
  | none => simp [core.option.OptionShared0T.cloned]
  | some value =>
    cases hclone : cloneInst.clone value <;> simp [core.option.OptionShared0T.cloned, hclone]

/-- Each optional vector lookup records its actual element-clone result.
Success supplies termination, and out-of-bounds positions stay absent. -/
theorem vec_clone_get_cloned {T : Type} (cloneInst : core.clone.Clone T)
    {self copied : alloc.vec.Vec T} (index : Nat)
    (hclone : alloc.vec.CloneVec.clone cloneInst self = ok copied) :
    core.option.OptionShared0T.cloned cloneInst self.val[index]? = ok copied.val[index]? := by
  have hmap := vec_clone_mapM cloneInst hclone
  have hlength := List.mapM_Result_length hmap
  by_cases hin : index < self.val.length
  · have hcopy : index < copied.val.length := by omega
    have hactual := List.mapM_Result_ok hmap index hin
    simp only [_root_.List.getElem?_eq_getElem hin, _root_.List.getElem?_eq_getElem hcopy,
      core.option.OptionShared0T.cloned, hactual, bind_tc_ok]
  · rw [_root_.List.getElem?_eq_none (by omega), _root_.List.getElem?_eq_none (by omega)]
    rfl

/-- At any retained vector slot, identity of the present source clone is
necessary and sufficient for equality of optional lookups. -/
theorem vec_clone_get_iff_clone_at {T : Type} (cloneInst : core.clone.Clone T)
    {self copied : alloc.vec.Vec T} (index : Nat)
    (hclone : alloc.vec.CloneVec.clone cloneInst self = ok copied) :
    copied.val[index]? = self.val[index]? ↔
      ∀ value, self.val[index]? = some value → cloneInst.clone value = ok value := by
  have hread := vec_clone_get_cloned cloneInst index hclone
  constructor
  · intro heq
    rw [heq] at hread
    exact (option_clone_identity_iff cloneInst self.val[index]?).mp hread
  · intro hidentity
    have hidentity := (option_clone_identity_iff cloneInst self.val[index]?).mpr hidentity
    exact Result.ok.inj (hread.symm.trans hidentity)

end milhouse_models
