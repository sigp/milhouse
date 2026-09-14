import Tree.PackedLeaf.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

/-- Replacing an existing position or appending at the end succeeds exactly
when the index has no gap and leaves room for the resulting vector length.
Neither cloning nor packing metadata is called by this operation. -/
theorem PackedLeaf.insert_mut_success {T : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (self : PackedLeaf T) (index : Std.Usize) (value : T)
    (hindex : index.val ≤ self.values.val.length)
    (hroom : index.val < Std.Usize.max) :
    ∃ result, PackedLeaf.insert_mut hashInst cloneInst self index value =
      ok (core.result.Result.Ok (), result) ∧
      result.values.val =
        if index.val = self.values.val.length then self.values.val ++ [value]
        else self.values.val.set index.val value := by
  have hsuccess : ∃ result, PackedLeaf.insert_mut hashInst cloneInst self index value =
      ok (core.result.Result.Ok (), result) := by
    by_cases hend : index = self.values.len
    · have hlen : self.values.val.length = index.val := by
        have := congrArg UScalar.val hend
        simpa only [alloc.vec.Vec.len_val] using this.symm
      obtain ⟨values, hpush, _⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec self.values value (by omega))
      refine ⟨{ hash := Array.repeat 32#usize 0#u8, values }, ?_⟩
      simp! only [PackedLeaf.insert_mut, lock_api.rwlock.RwLock.get_mut,
        alloy_primitives.bits.fixed.FixedBytes.ZERO, bind_tc_ok, hend,
        ↓reduceIte, hpush]
    · have hlt : index.val < self.values.val.length := by
        have hne : index.val ≠ self.values.val.length := by
          intro heq
          apply hend
          apply UScalar.eq_of_val_eq
          simpa only [alloc.vec.Vec.len_val] using heq
        omega
      obtain ⟨⟨old, back⟩, hmut, _, _⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_mut_usize_spec self.values index hlt)
      refine ⟨{ hash := Array.repeat 32#usize 0#u8, values := back value }, ?_⟩
      simp! only [PackedLeaf.insert_mut, lock_api.rwlock.RwLock.get_mut,
        alloy_primitives.bits.fixed.FixedBytes.ZERO, bind_tc_ok, hend,
        ↓reduceIte]
      have hlt' : index < self.values.len := by scalar_tac
      rw [if_pos hlt']
      rw [alloc.vec.Vec.index_mut_slice_index]
      simp! only [hmut, bind_tc_ok]
  obtain ⟨result, hinsert⟩ := hsuccess
  exact ⟨result, hinsert, (PackedLeaf.insert_mut_values hinsert).1⟩

/-- The insertion bounds are necessary as well as sufficient. In particular,
appending to a vector already at the machine maximum cannot succeed. -/
theorem PackedLeaf.insert_mut_success_iff {T : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (self : PackedLeaf T) (index : Std.Usize) (value : T) :
    (∃ result, PackedLeaf.insert_mut hashInst cloneInst self index value =
      ok (core.result.Result.Ok (), result)) ↔
      index.val ≤ self.values.val.length ∧ index.val < Std.Usize.max := by
  constructor
  · rintro ⟨result, hinsert⟩
    obtain ⟨hvalues, hindex⟩ := PackedLeaf.insert_mut_values hinsert
    refine ⟨hindex, ?_⟩
    have hbefore : self.values.val.length ≤ Std.Usize.max := by scalar_tac
    have hafter : result.values.val.length ≤ Std.Usize.max := by scalar_tac
    by_cases hend : index.val = self.values.val.length
    · rw [if_pos hend] at hvalues
      rw [hvalues] at hafter
      simp only [_root_.List.length_append, _root_.List.length_singleton] at hafter
      omega
    · omega
  · rintro ⟨hindex, hroom⟩
    obtain ⟨result, hinsert, _⟩ :=
      PackedLeaf.insert_mut_success hashInst cloneInst self index value hindex hroom
    exact ⟨result, hinsert⟩

end milhouse.packed_leaf
