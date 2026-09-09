import Tree.BulkUpdate.Activation
import Tree.BulkUpdate.Node
import Tree.BulkUpdate.RangeScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Success supplies the binary start condition. Only positive range answers
need pending witnesses; no false-answer, clone, query-termination, density, or
capacity law is assumed. The input condition merely rules out packed leaves
with unpacked metadata, which ordinary shape already excludes. -/
theorem Tree.with_updated_leaves_enabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hpacked : ∀ leaf, before = .PackedLeaf leaf → factor ≠ none)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hrange : BulkRangeOn (update_map.RangeSelectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (core.result.Result.Ok after)) :
    BulkUpdateEnabled mapInst updates factor depth.val (prefix1.val + offset.val) := by
  have node_enabled : ∀ hash left right,
      Tree.with_updated_leaves ValueInst mapInst (.Node hash left right) updates
        prefix1 offset depth hashes = ok (core.result.Result.Ok after) →
      BulkUpdateEnabled mapInst updates factor depth.val (prefix1.val + offset.val) := by
    intro hash left right hnode
    obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
      hnd, hrightPrefix, hlo, hmiddle, hstop, _, _, _, hselected⟩ :=
      Tree.with_updated_leaves_node_step_selected ValueInst mapInst hlayout halign hnode
    have hcap : subtreeCapacity factor depth.val = 2 * subtreeCapacity factor nd.val := by
      rw [hnd]
      simp only [subtreeCapacity, pow_succ]
      ring
    have hranges := hrange
    rw [hnd] at hranges
    have hsome : ∃ query, prefix1.val + offset.val ≤ query ∧
        query < prefix1.val + offset.val + subtreeCapacity factor depth.val ∧
        update_map.HasValueAt mapInst updates query := by
      rcases hselected with hleft | hright
      · obtain ⟨query, hlow, hhigh, hvalue⟩ :=
          (hranges.left_query hlo (by omega)) hleft
        exact ⟨query, by omega, by omega, hvalue⟩
      · obtain ⟨query, hlow, hhigh, hvalue⟩ :=
          (hranges.right_query (lo := middle) (hi := stop) (by omega) (by omega)) hright
        exact ⟨query, by omega, by omega, hvalue⟩
    obtain ⟨query, hlow, hhigh, hvalue⟩ := hsome
    refine Or.inr ⟨query - (prefix1.val + offset.val), by omega, ?_⟩
    have heq : prefix1.val + offset.val + (query - (prefix1.val + offset.val)) = query := by omega
    simpa only [heq] using hvalue
  cases before with
  | Leaf leaf =>
    obtain ⟨_, index, value, result, hindex, hget, _, _⟩ :=
      Tree.with_updated_leaves_leaf_cloned ValueInst mapInst hupdate
    refine Or.inr ⟨0, hlayout.subtreeCapacity_pos _, index, value, ?_, hget⟩
    simpa only [Nat.add_zero] using usize_add_val hindex
  | Node hash left right => exact node_enabled hash left right hupdate
  | PackedLeaf leaf =>
    unfold Tree.with_updated_leaves at hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨opt, _, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨hash, _, hupdate⟩ := hupdate
    dsimp only at hupdate
    by_cases hz : depth = 0#usize
    · exact Or.inl ⟨by rw [hz]; rfl, hpacked leaf rfl⟩
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
      · cases factor with
        | some factor => exact Or.inl ⟨by rw [hz]; rfl, by simp⟩
        | none =>
          rw [if_pos hz, hlayout.opt_packing_factor_eq] at hupdate
          simp only [bind_tc_ok, core.option.Option.is_some, Option.isSome,
            Bool.false_eq_true, if_false] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨index, hindex, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨found, hfound, hupdate⟩ := hupdate
          cases found with
          | none =>
            simp [core.option.OptionShared0T.cloned, core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | some value =>
            refine Or.inr ⟨0, hlayout.subtreeCapacity_pos _, index, value, ?_, hfound⟩
            simpa only [Nat.add_zero] using usize_add_val hindex
      · rw [if_neg hz, bind_eq_ok_iff] at hupdate
        obtain ⟨nd, _, hupdate⟩ := hupdate
        simp only [Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          bind_tc_ok] at hupdate
        exact node_enabled _ _ _ hupdate
    · simp [hsame] at hupdate

end milhouse.tree
