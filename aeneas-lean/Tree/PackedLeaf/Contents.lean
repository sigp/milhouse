import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

/-- Successful packed-leaf insertion either appends at the current end or
    replaces an existing value. This characterizes all values, not only length
    or read-back at the inserted index. Success supplies the bounds check. -/
theorem PackedLeaf.insert_mut_values {T : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {self updated : PackedLeaf T} {index : Std.Usize} {value : T}
    (hinsert : PackedLeaf.insert_mut thi cloneInst self index value =
      ok (core.result.Result.Ok (), updated)) :
    updated.values.val =
      (if index.val = self.values.val.length
       then self.values.val ++ [value] else self.values.val.set index.val value) ∧
      index.val ≤ self.values.val.length := by
  unfold PackedLeaf.insert_mut at hinsert
  simp [lock_api.rwlock.RwLock.get_mut,
    alloy_primitives.bits.fixed.FixedBytes.ZERO] at hinsert
  split at hinsert
  · next heq =>
    cases hpush : alloc.vec.Vec.push self.values value with
    | fail e => rw [hpush] at hinsert; simp at hinsert
    | div => rw [hpush] at hinsert; simp at hinsert
    | ok values =>
      rw [hpush] at hinsert
      simp at hinsert
      subst hinsert
      have hvalues : values.val = self.values.val ++ [value] := by
        unfold alloc.vec.Vec.push at hpush
        grind
      have hindex : index.val = self.values.val.length := by scalar_tac
      simp [hindex, hvalues]
  · next hne =>
    split at hinsert
    · next hlt =>
      cases hindex : alloc.vec.Vec.index_mut_usize self.values index with
      | fail e => rw [hindex] at hinsert; simp at hinsert
      | div => rw [hindex] at hinsert; simp at hinsert
      | ok pair =>
        rw [hindex] at hinsert
        obtain ⟨element, back⟩ := pair
        simp at hinsert
        unfold alloc.vec.Vec.index_mut_usize at hindex
        split at hindex <;>
          simp only [ok.injEq, Prod.mk.injEq, reduceCtorEq] at hindex
        obtain ⟨_, hback⟩ := hindex
        subst hback
        subst hinsert
        have hindex_ne : index.val ≠ self.values.val.length := by
          intro heqval
          apply hne
          scalar_tac
        simp [hindex_ne]
        omega
    · simp at hinsert

/-- A successful packed-leaf insertion changes exactly its selected element,
    preserving every other optional lookup, even beyond the old and new ends. -/
theorem PackedLeaf.get_after_insert_mut {T : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {self updated : PackedLeaf T} {index : Std.Usize} {value : T}
    (hinsert : PackedLeaf.insert_mut thi cloneInst self index value =
      ok (core.result.Result.Ok (), updated)) (query : Nat) :
    updated.values.val[query]? =
      if query = index.val then some value else self.values.val[query]? := by
  obtain ⟨hvalues, hbound⟩ := PackedLeaf.insert_mut_values hinsert
  rw [hvalues]
  by_cases hend : index.val = self.values.val.length
  · rw [if_pos hend]
    by_cases hquery : query = index.val
    · simp [hquery, hend]
    · rw [if_neg hquery]
      by_cases hlt : query < self.values.val.length
      · exact _root_.List.getElem?_append_left hlt
      · have hle : self.values.val.length ≤ query := by omega
        rw [_root_.List.getElem?_append_right hle]
        rw [_root_.List.getElem?_eq_none_iff.mpr hle,
          _root_.List.getElem?_eq_none_iff.mpr (by simp; omega)]
  · rw [if_neg hend]
    have hlt : index.val < self.values.val.length := by omega
    by_cases hquery : query = index.val
    · simp [hquery, hlt]
    · have hne : index.val ≠ query := Ne.symm hquery
      simp [hquery, hne]

end milhouse.packed_leaf
