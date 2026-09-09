import Tree.ProgressiveList.ToVec.Total

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Collecting a proved finite iterator appends its cloned values to the
    accumulator. The final length bound supplies every vector-push bound;
    cloning needs to preserve only values actually consumed by this loop. -/
theorem ProgressiveList.to_vec_loop_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T) (accumulator : alloc.vec.Vec T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) cursor values)
    (hbound : accumulator.val.length + values.length ≤ Std.Usize.max)
    (hclone : ∀ value ∈ values, ValueInst.corecloneCloneInst.clone value = ok value) :
    ∃ output, ProgressiveList.to_vec_loop ValueInst mapInst cursor accumulator = ok output ∧
      output.val = accumulator.val ++ values := by
  have hprojection := ProgressiveList.to_vec_loop_mapM
    ValueInst mapInst cursor values accumulator hyields hbound
  rw [milhouse_models.list_clone_identity ValueInst.corecloneCloneInst values hclone, bind_tc_ok] at hprojection
  cases hloop : ProgressiveList.to_vec_loop ValueInst mapInst cursor accumulator with
  | fail e => simp [hloop] at hprojection
  | div => simp [hloop] at hprojection
  | ok output =>
    exact ⟨output, rfl, by simpa only [hloop, bind_tc_ok, ok.injEq] using hprojection⟩

/-- `to_vec` succeeds and returns exactly the list's represented merged
    sequence, in order. The iterator theorem supplies complete traversal,
    representation supplies the vector bound, and only cloning the actual
    represented values is assumed. -/
theorem ProgressiveList.to_vec_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (hclone : ∀ value ∈ contents, ValueInst.corecloneCloneInst.clone value = ok value) :
    ∃ output, ProgressiveList.to_vec ValueInst mapInst self = ok output ∧ output.val = contents := by
  obtain ⟨output, hresult, hclones, _⟩ := ProgressiveList.to_vec_total_spec
    ValueInst mapInst hlayout self contents hrep hdense hfits (fun value hv => ⟨value, hclone value hv⟩)
  have hidentity := milhouse_models.list_clone_identity ValueInst.corecloneCloneInst contents hclone
  exact ⟨output, hresult, Result.ok.inj (hclones.symm.trans hidentity)⟩

end milhouse.progressive_list
