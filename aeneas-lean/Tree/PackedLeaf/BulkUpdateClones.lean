import Tree.PackedLeaf.BulkUpdate
import Tree.Vec.Clone

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Any returned packed-update result certifies cloning of all initial stored
values, including those later overwritten. No map, packing, clone identity,
input invariant, or successful Rust-result premise is needed. -/
theorem PackedLeaf.update_stored_clones_terminate {T U : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T)
    {self : PackedLeaf T} {start : Std.Usize} {updates : U}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    {result : core.result.Result (PackedLeaf T) error.Error}
    (hupdate : PackedLeaf.update hashInst cloneInst mapInst self start hash updates = ok result) :
    ∀ value ∈ self.values.val, ∃ copied, cloneInst.clone value = ok copied := by
  unfold PackedLeaf.update at hupdate
  simp only [lock_api.rwlock.RwLock.new, bind_tc_ok] at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨copied, hcopied, _⟩ := hupdate
  exact (milhouse_models.list_clone_success_iff cloneInst self.values.val).mp
    ⟨copied.val, milhouse_models.vec_clone_mapM cloneInst hcopied⟩

end milhouse.packed_leaf
