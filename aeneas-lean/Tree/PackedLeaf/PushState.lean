import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Every successful append stores exactly the old sequence followed by the
new value and invalidates the cached hash. No initial cache, clone, or packing
law is needed: successful execution supplies all checks and external calls. -/
theorem PackedLeaf.push_spec {T : Type}
    {hashInst : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {self result : PackedLeaf T} {value : T}
    (hpush : PackedLeaf.push hashInst cloneInst self value = ok (.Ok (), result)) :
    result.values.val = self.values.val ++ [value] ∧
      result.hash = Array.repeat 32#usize 0#u8 := by
  unfold PackedLeaf.push at hpush
  rw [bind_eq_ok_iff] at hpush
  obtain ⟨factor, _, hpush⟩ := hpush
  split at hpush
  · simp at hpush
  · rw [bind_eq_ok_iff] at hpush
    obtain ⟨values, hvalues, hpush⟩ := hpush
    simp [lock_api.rwlock.RwLock.get_mut, alloy_primitives.bits.fixed.FixedBytes.ZERO] at hpush
    subst result
    refine ⟨?_, rfl⟩
    unfold alloc.vec.Vec.push at hvalues
    grind

/-- A full leaf is rejected before either its values or its existing cache
changes. This covers arbitrary cached hashes, including a populated cache. -/
theorem PackedLeaf.push_full {T : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (self : PackedLeaf T) (value : T)
    (hfactor : hashInst.tree_hash_packing_factor = ok self.values.len) :
    PackedLeaf.push hashInst cloneInst self value =
      ok (.Err (.PackedLeafFull self.values.len), self) := by
  simp only [PackedLeaf.push, hfactor, bind_tc_ok, ↓reduceIte]

/-- Every returned Rust error leaves the complete leaf unchanged and is the
full-capacity error with the original length. Cache clearing occurs only
after the append succeeds. -/
theorem PackedLeaf.push_error_state {T : Type}
    {hashInst : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {self result : PackedLeaf T} {value : T} {error : error.Error}
    (hpush : PackedLeaf.push hashInst cloneInst self value = ok (.Err error, result)) :
    error = .PackedLeafFull self.values.len ∧ result = self := by
  unfold PackedLeaf.push at hpush
  rw [bind_eq_ok_iff] at hpush
  obtain ⟨factor, _, hpush⟩ := hpush
  split at hpush
  · simpa using hpush.symm
  · rw [bind_eq_ok_iff] at hpush
    obtain ⟨values, _, hpush⟩ := hpush
    simp [lock_api.rwlock.RwLock.get_mut, alloy_primitives.bits.fixed.FixedBytes.ZERO] at hpush

end milhouse.packed_leaf
