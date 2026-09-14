import Tree.BulkUpdate.Caches
import Tree.ProgressiveTree.HashCache
import Tree.ProgressiveTree.Depth

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- The tail expression of the extracted node update, parameterized by the
recursive function used in fixed-point induction. -/
private def finishCacheStep {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (recur : ProgressiveTree T → Std.U32 → Result (core.result.Result (ProgressiveTree T) error.Error))
    (maximum : Option Std.Usize) (next : Std.U32) (stop : Std.Usize)
    (left : tree.Tree T) (right : ProgressiveTree T) :
    Result (core.result.Result (ProgressiveTree T) error.Error) := do
  let b ← core.option.Option.is_some_and
    (ProgressiveTree.with_updated_leaves_recursive.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool
      ValueInst mapInst) maximum stop
  if b then
    let pt ← triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref right
    let result ← recur pt next
    let flow ← core.result.Result.Insts.CoreOpsTry.branch result
    match flow with
    | core.ops.control_flow.ControlFlow.Continue newRight =>
      let newRight ← triomphe.arc.Arc.new newRight
      let fb ← alloy_primitives.bits.fixed.FixedBytes.ZERO 32#usize
      let hash ← lock_api.rwlock.RwLock.new
        parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend fb
      ok (.Ok (.ProgressiveNode hash left newRight))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (ProgressiveTree T) (core.convert.FromSame error.Error) residual
  else
    let fb ← alloy_primitives.bits.fixed.FixedBytes.ZERO 32#usize
    let hash ← lock_api.rwlock.RwLock.new
      parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend fb
    ok (.Ok (.ProgressiveNode hash left right))

/-- Successful recursive progressive updates preserve all cache invariants
accepting zero. Checked execution itself supplies the binary and progressive
depth correspondence. No shape, density, packing, map, clone, or maximum law
is required, and the supplied maximum need not describe the pending map. -/
theorem ProgressiveTree.with_updated_leaves_recursive_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8)) (maximum : Option Std.Usize) :
    ∀ (before : ProgressiveTree T) (depth : Std.U32), before.CachesOn P depth.val →
      ∀ after, ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
        ok (.Ok after) → after.CachesOn P depth.val := by
  apply ProgressiveTree.with_updated_leaves_recursive.fixpoint_induct ValueInst mapInst updates maximum
    (fun recur => ∀ before depth, before.CachesOn P depth.val →
      ∀ after, recur before depth = ok (.Ok after) → after.CachesOn P depth.val)
  · apply Lean.Order.admissible_pi
    intro before
    apply Lean.Order.admissible_pi
    intro depth
    apply Lean.Order.admissible_pi
    intro hcache
    apply Lean.Order.admissible_pi
    intro after
    apply Lean.Order.admissible_apply (fun (_ : ProgressiveTree T)
      (f : Std.U32 → Result (core.result.Result (ProgressiveTree T) error.Error)) =>
      f depth = ok (.Ok after) → after.CachesOn P depth.val) before
    apply Lean.Order.admissible_apply (fun (_ : Std.U32)
      (value : Result (core.result.Result (ProgressiveTree T) error.Error)) =>
      value = ok (.Ok after) → after.CachesOn P depth.val) depth
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recur ih before depth hcache after hupdate
    dsimp! only at hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨start, _, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨next, hnext, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨stop, _, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨binary, hbinary, hupdate⟩ := hupdate
    have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
    have hnextVal : next.val = depth.val + 1 := by
      have h := UScalar.add_equiv depth 1#u32
      rw [hnext] at h
      simp at h
      omega
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨hasUpdates, _, hupdate⟩ := hupdate
    have finish (left : tree.Tree T) (right : ProgressiveTree T)
        (hl : left.CachesOn P (2 * depth.val)) (hr : right.CachesOn P next.val)
        (hfinish : finishCacheStep ValueInst mapInst recur maximum next stop left right = ok (.Ok after)) :
        after.CachesOn P depth.val := by
      unfold finishCacheStep at hfinish
      rw [bind_eq_ok_iff] at hfinish
      obtain ⟨hasRight, _, hfinish⟩ := hfinish
      cases hasRight with
      | false =>
        simp [alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new] at hfinish
        subst after
        exact ⟨hzero _, hl, by simpa only [hnextVal] using hr⟩
      | true =>
        simp only [if_true, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at hfinish
        rw [bind_eq_ok_iff] at hfinish
        obtain ⟨result, hresult, hfinish⟩ := hfinish
        cases result with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hfinish
        | Ok newRight =>
          simp [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new,
            alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new] at hfinish
          subst after
          exact ⟨hzero _, hl, by simpa only [hnextVal] using ih right next hr newRight hresult⟩
    have binaryCache (left : tree.Tree T) (hl : left.CachesOn P (2 * depth.val))
        {newLeft : tree.Tree T}
        (hleft : tree.Tree.with_updated_leaves ValueInst mapInst left updates 0#usize start binary none =
          ok (.Ok newLeft)) : newLeft.CachesOn P (2 * depth.val) := by
      have h := tree.Tree.with_updated_leaves_preserves_caches ValueInst mapInst updates P hzero
        start left 0#usize binary (by simpa only [hbinaryVal] using hl) newLeft hleft
      simpa only [hbinaryVal] using h
    cases before with
    | ProgressiveZero =>
      cases hasUpdates with
      | false =>
        simp at hupdate
        subst after
        trivial
      | true =>
        simp only [if_true, tree.Tree.zero, triomphe.arc.Arc.new,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨result, hresult, hupdate⟩ := hupdate
        cases result with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | Ok newLeft =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hupdate
          exact finish newLeft .ProgressiveZero (binaryCache (.Zero binary) trivial hresult) trivial hupdate
    | ProgressiveNode oldHash left right =>
      simp only [triomphe.arc.Arc.Insts.CoreCloneClone.clone, bind_tc_ok] at hupdate
      have hr : right.CachesOn P next.val := by simpa only [hnextVal] using hcache.2.2
      cases hasUpdates with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hupdate
        exact finish left right hcache.2.1 hr hupdate
      | true =>
        simp only [if_true, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok] at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨result, hresult, hupdate⟩ := hupdate
        cases result with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | Ok newLeft =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hupdate
          exact finish newLeft right (binaryCache left hcache.2.1 hresult) hr hupdate

/-- The public progressive bulk update preserves cache invariants using the
actual maximum returned by the map. No semantic condition on that answer is
needed for cache validity. -/
theorem ProgressiveTree.with_updated_leaves_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8))
    {before after : ProgressiveTree T} (hcache : before.CachesOn P 0)
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates = ok (.Ok after)) :
    after.CachesOn P 0 := by
  unfold ProgressiveTree.with_updated_leaves at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨maximum, _, hupdate⟩ := hupdate
  exact ProgressiveTree.with_updated_leaves_recursive_preserves_caches ValueInst mapInst updates P
    hzero maximum before 0#u32 hcache after hupdate

end milhouse.progressive_tree
