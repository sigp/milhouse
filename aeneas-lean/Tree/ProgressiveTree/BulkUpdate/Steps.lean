import Tree.ProgressiveTree

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- The right suffix is preserved precisely when the supplied maximum lies
    before it; otherwise the extracted recursive update succeeds on it. -/
def ProgressiveTree.BulkRightStep {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (next : Std.U32) (stop : Std.Usize)
    (before after : ProgressiveTree T) : Prop :=
  ((∀ index, maximum = some index → index.val < stop.val) ∧ after = before) ∨
  ((∃ index, maximum = some index ∧ stop.val ≤ index.val) ∧
    ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum next =
      ok (core.result.Result.Ok after))

/-- The three successful execution cases of one progressive spine step. This
    records actual range answers and recursive calls without imposing map laws. -/
inductive ProgressiveTree.BulkStep {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (next : Std.U32) (start stop binary : Std.Usize) :
    ProgressiveTree T → ProgressiveTree T → Prop where
  | zero
      (hmissing : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false) :
      BulkStep ValueInst mapInst updates maximum next start stop binary .ProgressiveZero .ProgressiveZero
  | expand {right : ProgressiveTree T} {newLeft : tree.Tree T}
      (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
      (hleft : tree.Tree.with_updated_leaves ValueInst mapInst (.Zero binary) updates
        0#usize start binary none = ok (core.result.Result.Ok newLeft))
      (hright : BulkRightStep ValueInst mapInst updates maximum next stop .ProgressiveZero right) :
      BulkStep ValueInst mapInst updates maximum next start stop binary .ProgressiveZero
        (.ProgressiveNode hash newLeft right)
  | node {left newLeft : tree.Tree T} {right newRight : ProgressiveTree T}
      (oldHash newHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hleft :
        (ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok false ∧
          newLeft = left) ∨
        (ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true ∧
          tree.Tree.with_updated_leaves ValueInst mapInst left updates 0#usize start binary none =
            ok (core.result.Result.Ok newLeft)))
      (hright : BulkRightStep ValueInst mapInst updates maximum next stop right newRight) :
      BulkStep ValueInst mapInst updates maximum next start stop binary
        (.ProgressiveNode oldHash left right) (.ProgressiveNode newHash newLeft newRight)

private def finishNode {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (next : Std.U32) (stop : Std.Usize)
    (left : tree.Tree T) (right : ProgressiveTree T) :
    Result (core.result.Result (ProgressiveTree T) error.Error) := do
  let b ← core.option.Option.is_some_and
    (ProgressiveTree.with_updated_leaves_recursive.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool
      ValueInst mapInst) maximum stop
  if b then
    let pt ← triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref right
    let r ← ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst pt updates maximum next
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue newRight =>
      let newRight ← triomphe.arc.Arc.new newRight
      let fb ← alloy_primitives.bits.fixed.FixedBytes.ZERO 32#usize
      let hash ← lock_api.rwlock.RwLock.new
        parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend fb
      ok (core.result.Result.Ok (.ProgressiveNode hash left newRight))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (ProgressiveTree T) (core.convert.FromSame error.Error) residual
  else
    let fb ← alloy_primitives.bits.fixed.FixedBytes.ZERO 32#usize
    let hash ← lock_api.rwlock.RwLock.new
      parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend fb
    ok (core.result.Result.Ok (.ProgressiveNode hash left right))

private theorem finishNode_step {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {maximum : Option Std.Usize} {next : Std.U32} {stop : Std.Usize}
    {left : tree.Tree T} {right after : ProgressiveTree T}
    (hfinish : finishNode ValueInst mapInst updates maximum next stop left right =
      ok (core.result.Result.Ok after)) :
    ∃ hash newRight, after = .ProgressiveNode hash left newRight ∧
      ProgressiveTree.BulkRightStep ValueInst mapInst updates maximum next stop right newRight := by
  unfold finishNode at hfinish
  cases maximum with
  | none =>
    simp [core.option.Option.is_some_and, alloy_primitives.bits.fixed.FixedBytes.ZERO,
      lock_api.rwlock.RwLock.new] at hfinish
    exact ⟨_, right, hfinish.symm, Or.inl ⟨by simp, rfl⟩⟩
  | some largest =>
    simp only [core.option.Option.is_some_and,
      ProgressiveTree.with_updated_leaves_recursive.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once,
      bind_tc_ok, decide_eq_true_eq] at hfinish
    by_cases hlarge : largest ≥ stop
    · simp only [if_pos hlarge, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
        bind_tc_ok] at hfinish
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
        exact ⟨_, newRight, hfinish.symm, Or.inr ⟨⟨largest, rfl, by scalar_tac⟩, hresult⟩⟩
    · simp only [if_neg hlarge] at hfinish
      simp [alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new] at hfinish
      refine ⟨_, right, hfinish.symm, Or.inl ⟨?_, rfl⟩⟩
      intro index hindex
      cases hindex
      scalar_tac

/-- Every successful recursive update decomposes into checked layer geometry
    and one of the exact execution cases above, including the zero early exit
    and both recursive error paths. No shape or map-semantic premise is used. -/
theorem ProgressiveTree.with_updated_leaves_recursive_step {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {before after : ProgressiveTree T} {updates : U}
    {maximum : Option Std.Usize} {depth : Std.U32}
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (core.result.Result.Ok after)) :
    ∃ start next stop binary,
      ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start ∧
      depth + 1#u32 = ok next ∧
      ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop ∧
      ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary ∧
      ProgressiveTree.BulkStep ValueInst mapInst updates maximum next start stop binary before after := by
  unfold ProgressiveTree.with_updated_leaves_recursive at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨start, hstart, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨next, hnext, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨stop, hstop, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨binary, hbinary, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨hasUpdates, hhas, hupdate⟩ := hupdate
  refine ⟨start, next, stop, binary, hstart, hnext, hstop, hbinary, ?_⟩
  cases before with
  | ProgressiveZero =>
    cases hasUpdates with
    | false =>
      simp at hupdate
      subst after
      exact .zero hhas
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
        change finishNode ValueInst mapInst updates maximum next stop newLeft .ProgressiveZero = _ at hupdate
        obtain ⟨hash, newRight, rfl, hright⟩ := finishNode_step ValueInst mapInst updates hupdate
        exact .expand hash hhas hresult hright
  | ProgressiveNode oldHash left right =>
    simp only [triomphe.arc.Arc.Insts.CoreCloneClone.clone, bind_tc_ok] at hupdate
    cases hasUpdates with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hupdate
      change finishNode ValueInst mapInst updates maximum next stop left right = _ at hupdate
      obtain ⟨hash, newRight, rfl, hright⟩ := finishNode_step ValueInst mapInst updates hupdate
      exact .node oldHash hash (Or.inl ⟨hhas, rfl⟩) hright
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
        change finishNode ValueInst mapInst updates maximum next stop newLeft right = _ at hupdate
        obtain ⟨hash, newRight, rfl, hright⟩ := finishNode_step ValueInst mapInst updates hupdate
        exact .node oldHash hash (Or.inr ⟨hhas, hresult⟩) hright

end milhouse.progressive_tree
