import Tree.ProgressiveList.Iter.Traits
import Tree.ProgressiveList.Iter.Length

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
  induction hyields generalizing accumulator with
  | nil hnext =>
    refine ⟨accumulator, ?_, by simp⟩
    rw [ProgressiveList.to_vec_loop, loop]
    simp! only [ProgressiveList.to_vec_loop.body, hnext, bind_tc_ok]
  | @cons cursor rest value values hnext hyields ih =>
    have hroom : accumulator.val.length < Std.Usize.max := by
      simp only [_root_.List.length_cons] at hbound
      omega
    obtain ⟨pushed, hpush, hpushed⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec accumulator value hroom)
    have htailBound : pushed.val.length + values.length ≤ Std.Usize.max := by
      rw [hpushed]
      simp only [_root_.List.length_append, _root_.List.length_cons, _root_.List.length_nil] at hbound ⊢
      omega
    obtain ⟨output, hloop, houtput⟩ := ih pushed htailBound (fun item hitem => hclone item (by simp [hitem]))
    refine ⟨output, ?_, ?_⟩
    · rw [ProgressiveList.to_vec_loop, loop]
      simp! only [ProgressiveList.to_vec_loop.body, hnext, bind_tc_ok,
        hclone value (by simp), hpush]
      exact hloop
    · simpa [hpushed, _root_.List.append_assoc] using houtput

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
  obtain ⟨cursor, hiter, hvalid, _, hyields⟩ :=
    ProgressiveList.into_iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  have hlength := @ProgressiveListIter.Valid.length_eq T U ValueInst mapInst factor self.tree.elements contents cursor hvalid
  obtain ⟨remaining, hremaining, _⟩ := ProgressiveListIter.exact_len_spec ValueInst mapInst cursor contents hlength
  let accumulator := alloc.vec.Vec.with_capacity T remaining
  have hempty : accumulator.val = [] := rfl
  have hbound : accumulator.val.length + contents.length ≤ Std.Usize.max := by
    rw [hempty]
    simp only [_root_.List.length_nil, Nat.zero_add]
    rw [← hlength]
    scalar_tac
  obtain ⟨output, hloop, houtput⟩ :=
    ProgressiveList.to_vec_loop_spec ValueInst mapInst cursor contents accumulator hyields hbound hclone
  refine ⟨output, ?_, ?_⟩
  · simp only [ProgressiveList.to_vec, hiter, bind_tc_ok, hremaining]
    exact hloop
  · simpa [hempty] using houtput

end milhouse.progressive_list
