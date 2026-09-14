import Tree.BulkUpdate.Node

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- A successful binary bulk rebuild always constructs a leaf or node,
including when it expands zero padding. It never returns a `Zero` tree. -/
theorem Tree.with_updated_leaves_ne_zero {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {before after : Tree T} {updates : U} {prefix1 offset depth zeroDepth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    after ≠ .Zero zeroDepth := by
  have node_ne_zero : ∀ hash left right,
      Tree.with_updated_leaves ValueInst mapInst (.Node hash left right) updates prefix1 offset depth hashes =
        ok (core.result.Result.Ok after) → after ≠ .Zero zeroDepth := by
    intro hash left right hnode
    unfold Tree.with_updated_leaves at hnode
    rw [bind_eq_ok_iff] at hnode
    obtain ⟨opt, _, hnode⟩ := hnode
    rw [bind_eq_ok_iff] at hnode
    obtain ⟨hash, _, hnode⟩ := hnode
    change (if depth > 0#usize then _ else _) = _ at hnode
    by_cases hpositive : depth > 0#usize
    · rw [if_pos hpositive] at hnode
      simp only [lift, bind_tc_ok, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨packing, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨nd, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨shift, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨stride, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨parentShift, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨width, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨subtreeEnd, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨lo, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨middle, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨bl, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨stop, _, hnode⟩ := hnode
      rw [bind_eq_ok_iff] at hnode
      obtain ⟨br, _, hnode⟩ := hnode
      cases bl with
      | false =>
        cases br with
        | false => simp at hnode
        | true =>
          simp only [Bool.false_eq_true, if_false, if_true] at hnode
          rw [bind_eq_ok_iff] at hnode
          obtain ⟨result, _, hnode⟩ := hnode
          cases result with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hnode
          | Ok right =>
            simp [core.result.Result.Insts.CoreOpsTry.branch, Tree.node,
              lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hnode
            subst after
            intro hzero
            cases hzero
      | true =>
        simp only [if_true] at hnode
        rw [bind_eq_ok_iff] at hnode
        obtain ⟨result, _, hnode⟩ := hnode
        cases result with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hnode
        | Ok left =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hnode
          cases br with
          | false =>
            simp [Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hnode
            subst after
            intro hzero
            cases hzero
          | true =>
            simp only [if_true] at hnode
            rw [bind_eq_ok_iff] at hnode
            obtain ⟨result, _, hnode⟩ := hnode
            cases result with
            | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hnode
            | Ok right =>
              simp [Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hnode
              subst after
              intro hzero
              cases hzero
    · simp [hpositive] at hnode
  cases before with
  | Leaf leaf =>
    obtain ⟨_, rfl⟩ := with_updated_leaves_leaf_shape hupdate
    intro hzero
    cases hzero
  | Node hash left right => exact node_ne_zero hash left right hupdate
  | PackedLeaf leaf =>
    unfold Tree.with_updated_leaves at hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨opt, _, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨hash, _, hupdate⟩ := hupdate
    dsimp only at hupdate
    by_cases hz : depth = 0#usize
    · rw [if_pos hz, bind_eq_ok_iff] at hupdate
      obtain ⟨start, _, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨result, _, hupdate⟩ := hupdate
      cases result with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hupdate
      | Ok leaf =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, triomphe.arc.Arc.new,
          Result.ok.injEq, core.result.Result.Ok.injEq] at hupdate
        subst after
        intro hzero
        cases hzero
    · simp [hz] at hupdate
  | Zero oldDepth =>
    unfold Tree.with_updated_leaves at hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨opt, _, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨hash, _, hupdate⟩ := hupdate
    dsimp only at hupdate
    by_cases hsame : oldDepth = depth
    · rw [if_pos hsame] at hupdate
      by_cases hz : depth = 0#usize
      · rw [if_pos hz, bind_eq_ok_iff] at hupdate
        obtain ⟨factor, _, hupdate⟩ := hupdate
        cases factor with
        | none =>
          simp only [core.option.Option.is_some, Option.isSome, Bool.false_eq_true, if_false] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨index, _, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨found, _, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨cloned, _, hupdate⟩ := hupdate
          cases cloned with
          | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | some value =>
            simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
              bind_tc_ok, Tree.leaf_with_hash, leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new,
              triomphe.arc.Arc.new, Result.ok.injEq, core.result.Result.Ok.injEq] at hupdate
            subst after
            intro hzero
            cases hzero
        | some factor =>
          simp only [core.option.Option.is_some, Option.isSome, if_true] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨empty, _, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨start, _, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨result, _, hupdate⟩ := hupdate
          cases result with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok leaf =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, triomphe.arc.Arc.new,
              Result.ok.injEq, core.result.Result.Ok.injEq] at hupdate
            subst after
            intro hzero
            cases hzero
      · rw [if_neg hz, bind_eq_ok_iff] at hupdate
        obtain ⟨nd, _, hupdate⟩ := hupdate
        simp only [Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          bind_tc_ok] at hupdate
        exact node_ne_zero _ _ _ hupdate
    · simp [hsame] at hupdate

/-- A successfully rebuilt binary tree which is dense has positive length.
This is a consequence of its actual output shape, not a pending-value law. -/
theorem Tree.with_updated_leaves_dense_length_pos {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {factor : Option Std.Usize} {treeDepth length : Nat}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after))
    (hdense : DenseTree factor after treeDepth length) : 0 < length := by
  by_contra hnot
  obtain ⟨zeroDepth, hzero, _⟩ := hdense.eq_zero_of_length_zero (by omega)
  exact Tree.with_updated_leaves_ne_zero ValueInst mapInst hupdate hzero

end milhouse.tree
