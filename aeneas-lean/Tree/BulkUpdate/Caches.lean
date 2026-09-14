import Tree.HashCache
import Tree.PackedLeaf.Caches
import Tree.Arithmetic

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Without precomputed hashes, successful binary bulk updates preserve any
cache invariant accepting the zero sentinel. Modified caches are cleared and
unchanged children are shared as before. This needs no shape, packing-layout,
alignment, clone-identity, map-semantic, or termination premise. -/
theorem Tree.with_updated_leaves_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8)) (offset : Std.Usize) :
    ∀ (before : Tree T) (prefix1 depth : Std.Usize), before.CachesOn P depth.val →
      ∀ after, Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth none =
        ok (.Ok after) → after.CachesOn P depth.val := by
  apply Tree.with_updated_leaves.fixpoint_induct ValueInst mapInst updates offset none
    (fun recur => ∀ before prefix1 depth, before.CachesOn P depth.val →
      ∀ after, recur before prefix1 depth = ok (.Ok after) → after.CachesOn P depth.val)
  · apply Lean.Order.admissible_pi
    intro before
    apply Lean.Order.admissible_pi
    intro prefix1
    apply Lean.Order.admissible_pi
    intro depth
    apply Lean.Order.admissible_pi
    intro hcache
    apply Lean.Order.admissible_pi
    intro after
    apply Lean.Order.admissible_apply (fun (_ : Tree T)
      (f : Std.Usize → Std.Usize → Result (core.result.Result (Tree T) error.Error)) =>
      f prefix1 depth = ok (.Ok after) → after.CachesOn P depth.val) before
    apply Lean.Order.admissible_apply (fun (_ : Std.Usize)
      (f : Std.Usize → Result (core.result.Result (Tree T) error.Error)) =>
      f depth = ok (.Ok after) → after.CachesOn P depth.val) prefix1
    apply Lean.Order.admissible_apply (fun (_ : Std.Usize)
      (value : Result (core.result.Result (Tree T) error.Error)) =>
      value = ok (.Ok after) → after.CachesOn P depth.val) depth
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recur ih before prefix1 depth hcache after hupdate
    dsimp! only at hupdate
    simp only [utils.opt_hash, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      core.option.Option.unwrap_or_default,
      alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault.default,
      bind_tc_ok] at hupdate
    have packedCache (leaf : packed_leaf.PackedLeaf T) (start : Std.Usize)
        {result : packed_leaf.PackedLeaf T}
        (hpacked : packed_leaf.PackedLeaf.update ValueInst.tree_hashTreeHashInst
          ValueInst.corecloneCloneInst mapInst leaf start (Array.repeat 32#usize 0#u8) updates =
          ok (.Ok result)) : P (.packed result.values.val) result.hash := by
      rw [packed_leaf.PackedLeaf.update_zero_hash hpacked]
      exact hzero _
    cases before with
    | Leaf leaf =>
      simp only at hupdate
      split at hupdate
      · rw [bind_eq_ok_iff] at hupdate
        obtain ⟨index, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨found, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨cloned, _, hupdate⟩ := hupdate
        cases cloned with
        | none =>
          simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | some value =>
          simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            Tree.leaf_with_hash, milhouse.leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new,
            triomphe.arc.Arc.new] at hupdate
          subst after
          exact hzero _
      · simp at hupdate
    | PackedLeaf leaf =>
      simp only at hupdate
      split at hupdate
      · rw [bind_eq_ok_iff] at hupdate
        obtain ⟨start, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨result, hresult, hupdate⟩ := hupdate
        cases result with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | Ok result =>
          simp [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new] at hupdate
          subst after
          exact packedCache leaf start hresult
      · simp at hupdate
    | Node hash left right =>
      simp only at hupdate
      split at hupdate
      · rw [bind_eq_ok_iff] at hupdate
        obtain ⟨packing, _, hupdate⟩ := hupdate
        simp only [lift, bind_tc_ok, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨nd, hnd, hupdate⟩ := hupdate
        have hndVal := usize_sub_one_val hnd
        have hleftCache : left.CachesOn P nd.val := by
          simpa only [hndVal, Nat.add_sub_cancel] using hcache.2.1
        have hrightCache : right.CachesOn P nd.val := by
          simpa only [hndVal, Nat.add_sub_cancel] using hcache.2.2
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨shift, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨stride, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨parentShift, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨width, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨stop, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨lo, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨middle, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨hasLeft, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨hi, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨hasRight, _, hupdate⟩ := hupdate
        have finish (newLeft newRight : Tree T)
            (hl : newLeft.CachesOn P nd.val) (hr : newRight.CachesOn P nd.val) :
            (Tree.Node (Array.repeat 32#usize 0#u8) newLeft newRight).CachesOn P depth.val := by
          simp only [Tree.CachesOn, hndVal, Nat.add_sub_cancel]
          exact ⟨hzero _, hl, hr⟩
        cases hasLeft with
        | false =>
          cases hasRight with
          | false => simp at hupdate
          | true =>
            simp only [Bool.false_eq_true, if_false, if_true] at hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨result, hresult, hupdate⟩ := hupdate
            cases result with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hupdate
            | Ok newRight =>
              simp [core.result.Result.Insts.CoreOpsTry.branch, Tree.node,
                lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
              subst after
              exact finish left newRight hleftCache (ih _ _ _ hrightCache _ hresult)
        | true =>
          simp only [if_true] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨result, hresult, hupdate⟩ := hupdate
          cases result with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok newLeft =>
            have hnewLeft := ih _ _ _ hleftCache _ hresult
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hupdate
            cases hasRight with
            | false =>
              simp [Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
              subst after
              exact finish newLeft right hnewLeft hrightCache
            | true =>
              simp only [if_true] at hupdate
              rw [bind_eq_ok_iff] at hupdate
              obtain ⟨result, hresult, hupdate⟩ := hupdate
              cases result with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hupdate
              | Ok newRight =>
                simp [Tree.node,
                  lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
                subst after
                exact finish newLeft newRight hnewLeft (ih _ _ _ hrightCache _ hresult)
      · simp at hupdate
    | Zero zeroDepth =>
      simp only at hupdate
      split at hupdate
      · split at hupdate
        · rw [bind_eq_ok_iff] at hupdate
          obtain ⟨packing, _, hupdate⟩ := hupdate
          cases packing with
          | none =>
            simp only [core.option.Option.is_some, Option.isSome, Bool.false_eq_true, if_false] at hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨index, _, hupdate⟩ := hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨found, _, hupdate⟩ := hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨cloned, _, hupdate⟩ := hupdate
            cases cloned with
            | none =>
              simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hupdate
            | some value =>
              simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
                Tree.leaf_with_hash, leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new,
                triomphe.arc.Arc.new] at hupdate
              subst after
              exact hzero _
          | some packing =>
            simp only [core.option.Option.is_some, Option.isSome, if_true] at hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨leaf, _, hupdate⟩ := hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨start, _, hupdate⟩ := hupdate
            rw [bind_eq_ok_iff] at hupdate
            obtain ⟨result, hresult, hupdate⟩ := hupdate
            cases result with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hupdate
            | Ok result =>
              simp [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new] at hupdate
              subst after
              exact packedCache leaf start hresult
        · rw [bind_eq_ok_iff] at hupdate
          obtain ⟨nd, _, hupdate⟩ := hupdate
          simp only [Tree.zero, Tree.node, triomphe.arc.Arc.new,
            triomphe.arc.Arc.Insts.CoreCloneClone.clone, lock_api.rwlock.RwLock.new,
            triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at hupdate
          exact ih (.Node (Array.repeat 32#usize 0#u8) (.Zero nd) (.Zero nd)) prefix1 depth
            ⟨hzero _, trivial, trivial⟩ _ hupdate
      · simp at hupdate

end milhouse.tree
