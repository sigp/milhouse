import Tree.ProgressiveList.Iter.Traits

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The actual collection loop appends the ordered results of element
cloning, including the exact first failure or divergence. Finite iterator
enumeration and the final length bound justify all iteration and vector
pushes; no clone identity or clone termination is assumed. -/
theorem ProgressiveList.to_vec_loop_mapM {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T) (accumulator : alloc.vec.Vec T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst) cursor values)
    (hbound : accumulator.val.length + values.length ≤ Std.Usize.max) :
    (do let output ← ProgressiveList.to_vec_loop ValueInst mapInst accumulator cursor
        ok output.val) =
      (do let cloned ← _root_.List.mapM ValueInst.corecloneCloneInst.clone values
          ok (accumulator.val ++ cloned)) := by
  induction hyields generalizing accumulator with
  | nil hnext =>
    rw [ProgressiveList.to_vec_loop, loop]
    simp! only [ProgressiveList.to_vec_loop.body, hnext, bind_tc_ok,
      _root_.List.mapM_nil, Pure.pure, _root_.List.append_nil]
  | @cons cursor rest value values hnext hyields ih =>
    rw [ProgressiveList.to_vec_loop, loop]
    simp! only [ProgressiveList.to_vec_loop.body, hnext, bind_tc_ok, _root_.List.mapM_cons]
    cases hclone : ValueInst.corecloneCloneInst.clone value with
    | fail e => simp
    | div => simp
    | ok cloned =>
      have hroom : accumulator.val.length < Std.Usize.max := by
        simp only [_root_.List.length_cons] at hbound
        omega
      obtain ⟨pushed, hpush, hpushed⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec accumulator cloned hroom)
      have htailBound : pushed.val.length + values.length ≤ Std.Usize.max := by
        rw [hpushed]
        simp only [_root_.List.length_append, _root_.List.length_cons, _root_.List.length_nil] at hbound ⊢
        omega
      simp only [hpush, bind_tc_ok]
      have htail := ih pushed htailBound
      simp! only [ProgressiveList.to_vec_loop, ProgressiveList.to_vec_loop.body,
        hpushed, Pure.pure, bind_assoc_eq, bind_tc_ok, _root_.List.append_assoc,
        _root_.List.cons_append, _root_.List.nil_append] at htail ⊢
      exact htail

end milhouse.progressive_list
