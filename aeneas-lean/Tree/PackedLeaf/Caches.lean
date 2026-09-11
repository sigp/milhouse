import Tree.PackedLeaf.PushState
import Tree.Loop

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Insertion clears the cache before checking the index. Every returned
state therefore has a zero cache, including an out-of-bounds Rust error. -/
theorem PackedLeaf.insert_mut_clears_hash {T : Type}
    {hashInst : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {self result : PackedLeaf T} {index : Std.Usize} {value : T}
    {outcome : core.result.Result Unit error.Error}
    (hinsert : PackedLeaf.insert_mut hashInst cloneInst self index value = ok (outcome, result)) :
    result.hash = Array.repeat 32#usize 0#u8 := by
  unfold PackedLeaf.insert_mut at hinsert
  simp only [lock_api.rwlock.RwLock.get_mut, alloy_primitives.bits.fixed.FixedBytes.ZERO,
    bind_tc_ok] at hinsert
  dsimp! only at hinsert
  split at hinsert
  · rw [bind_eq_ok_iff] at hinsert
    obtain ⟨values, _, hinsert⟩ := hinsert
    simp only [ok.injEq, Prod.mk.injEq] at hinsert
    obtain ⟨_, rfl⟩ := hinsert
    rfl
  · split at hinsert
    · rw [bind_eq_ok_iff] at hinsert
      obtain ⟨⟨_, back⟩, _, hinsert⟩ := hinsert
      dsimp! only at hinsert
      simp only [ok.injEq, Prod.mk.injEq] at hinsert
      obtain ⟨_, rfl⟩ := hinsert
      rfl
    · simp only [ok.injEq, Prod.mk.injEq] at hinsert
      obtain ⟨_, rfl⟩ := hinsert
      rfl

/-- The owning insertion result has an invalidated cache independently of
the old cache and of the values produced by cloning. -/
theorem PackedLeaf.insert_at_index_clears_hash {T : Type}
    {hashInst : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {self result : PackedLeaf T} {index : Std.Usize} {value : T}
    (hinsert : PackedLeaf.insert_at_index hashInst cloneInst self index value = ok (.Ok result)) :
    result.hash = Array.repeat 32#usize 0#u8 := by
  unfold PackedLeaf.insert_at_index at hinsert
  simp only [alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new,
    bind_tc_ok] at hinsert
  rw [bind_eq_ok_iff] at hinsert
  obtain ⟨values, _, hinsert⟩ := hinsert
  rw [bind_eq_ok_iff] at hinsert
  obtain ⟨factor, _, hinsert⟩ := hinsert
  rw [bind_eq_ok_iff] at hinsert
  obtain ⟨sub, _, hinsert⟩ := hinsert
  rw [bind_eq_ok_iff] at hinsert
  obtain ⟨⟨outcome, updated⟩, hupdated, hinsert⟩ := hinsert
  cases outcome with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at hinsert
  | Ok u =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hinsert
    subst result
    exact PackedLeaf.insert_mut_clears_hash hupdated

/-- The update scan either retains its initial hash or clears it on insertion.
This follows from successful execution alone, without map, clone, alignment,
or scan-termination assumptions. -/
theorem PackedLeaf.update_loop_hash {T U : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (updates : U)
    (self : PackedLeaf T) (factor stop index : Std.Usize) {result : PackedLeaf T}
    (hloop : PackedLeaf.update_loop hashInst cloneInst mapInst updates self factor stop index =
      ok (.Ok result)) :
    result.hash = self.hash ∨ result.hash = Array.repeat 32#usize 0#u8 := by
  let inv : PackedLeaf T × Std.Usize → Prop := fun state =>
    state.1.hash = self.hash ∨ state.1.hash = Array.repeat 32#usize 0#u8
  let post : core.result.Result (PackedLeaf T) error.Error → Prop := fun outcome =>
    match outcome with
    | .Ok leaf => leaf.hash = self.hash ∨ leaf.hash = Array.repeat 32#usize 0#u8
    | .Err _ => True
  apply loop_success_invariant
    (fun state : PackedLeaf T × Std.Usize =>
      PackedLeaf.update_loop.body hashInst cloneInst mapInst updates factor stop state.1 state.2)
    inv post ?_ (self, index) (Or.inl rfl) (.Ok result) hloop
  rintro ⟨leaf, nextIndex⟩ hcache flow hbody
  unfold PackedLeaf.update_loop.body at hbody
  split at hbody
  · rw [bind_eq_ok_iff] at hbody
    obtain ⟨found, _, hbody⟩ := hbody
    cases found with
    | none =>
      rw [bind_eq_ok_iff] at hbody
      obtain ⟨next, _, hbody⟩ := hbody
      simp only [ok.injEq] at hbody
      subst flow
      exact hcache
    | some value =>
      rw [bind_eq_ok_iff] at hbody
      obtain ⟨sub, _, hbody⟩ := hbody
      rw [bind_eq_ok_iff] at hbody
      obtain ⟨cloned, _, hbody⟩ := hbody
      rw [bind_eq_ok_iff] at hbody
      obtain ⟨⟨outcome, updated⟩, hupdated, hbody⟩ := hbody
      dsimp! only at hbody
      cases outcome with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hbody
        subst flow
        trivial
      | Ok u =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hbody
        rw [bind_eq_ok_iff] at hbody
        obtain ⟨next, _, hbody⟩ := hbody
        simp only [ok.injEq] at hbody
        subst flow
        exact Or.inr (PackedLeaf.insert_mut_clears_hash hupdated)
  · simp only [ok.injEq] at hbody
    subst flow
    exact hcache

/-- A successful packed bulk update returns the supplied hash or zero. The
old stored cache is discarded even if the map produces no insertions. -/
theorem PackedLeaf.update_hash {T U : Type}
    {hashInst : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {start : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    (hupdate : PackedLeaf.update hashInst cloneInst mapInst self start hash updates = ok (.Ok result)) :
    result.hash = hash ∨ result.hash = Array.repeat 32#usize 0#u8 := by
  unfold PackedLeaf.update at hupdate
  simp only [lock_api.rwlock.RwLock.new, bind_tc_ok] at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨values, _, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨factor, _, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨stop, _, hupdate⟩ := hupdate
  exact PackedLeaf.update_loop_hash hashInst cloneInst mapInst updates
    { hash, values } factor stop start hupdate

/-- With no precomputed hash, a successful packed bulk update always returns
a zero cache, even when cloning changes the copied or inserted values. -/
theorem PackedLeaf.update_zero_hash {T U : Type}
    {hashInst : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {start : Std.Usize}
    (hupdate : PackedLeaf.update hashInst cloneInst mapInst self start
      (Array.repeat 32#usize 0#u8) updates = ok (.Ok result)) :
    result.hash = Array.repeat 32#usize 0#u8 :=
  (PackedLeaf.update_hash hupdate).elim id id

end milhouse.packed_leaf
