import Tree.Rebase

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- A successful progressive rebase either keeps the original tree or rebuilds
    one node from the actual binary action and recursive suffix result. The
    node case records all metadata calculations used by those calls. -/
inductive ProgressiveTree.RebaseStep {T : Type} (ValueInst : Value T)
    (origLength baseLength : Std.Usize) (depth : Std.U32) (packingDepth : Std.Usize) :
    ProgressiveTree T → ProgressiveTree T → ProgressiveTree T → Prop where
  | same (orig base : ProgressiveTree T) : RebaseStep ValueInst origLength baseLength depth packingDepth orig base orig
  | node
      {origHash baseHash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
      {origLeft baseLeft : tree.Tree T} {origRight baseRight newRight : ProgressiveTree T}
      {start capacity binary fullDepth origLeftLength baseLeftLength : Std.Usize} {next : Std.U32}
      (action : tree.RebaseAction (tree.Tree T))
      (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
      (hnext : depth + 1#u32 = ok next)
      (hcapacity : ProgressiveTree.capacity_at_depth ValueInst next = ok capacity)
      (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
      (horigLength : core.cmp.Ord.min.trait_default core.cmp.OrdUsize
        (core.num.Usize.saturating_sub origLength start) capacity = ok origLeftLength)
      (hbaseLength : core.cmp.Ord.min.trait_default core.cmp.OrdUsize
        (core.num.Usize.saturating_sub baseLength start) capacity = ok baseLeftLength)
      (hfullDepth : binary + packingDepth = ok fullDepth)
      (hleft : tree.Tree.rebase_on ValueInst origLeft baseLeft
        (some (origLeftLength, baseLeftLength)) fullDepth = ok (core.result.Result.Ok action))
      (hright : ProgressiveTree.rebase_on_recursive ValueInst origRight baseRight origLength baseLength next =
        ok (core.result.Result.Ok newRight)) :
      RebaseStep ValueInst origLength baseLength depth packingDepth
        (.ProgressiveNode origHash origLeft origRight) (.ProgressiveNode baseHash baseLeft baseRight)
        (.ProgressiveNode origHash (tree.applyRebaseAction origLeft action) newRight)

/-- Operational decomposition of successful progressive rebasing. Pointer
    equality uses the existing model law; no density, length, equality, or
    hash-correctness assumption is required. -/
theorem ProgressiveTree.rebase_on_recursive_step {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (core.result.Result.Ok after)) :
    ProgressiveTree.RebaseStep ValueInst origLength baseLength depth packingDepth orig base after := by
  unfold ProgressiveTree.rebase_on_recursive at hrebase
  obtain ⟨pointerEqual, hpointer, hpointerTrue⟩ := triomphe.arc.Arc.ptr_eq_spec orig base
  rw [hpointer] at hrebase
  cases pointerEqual with
  | true =>
    simp [triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hrebase
    subst after
    rw [← hpointerTrue rfl]
    exact .same orig orig
  | false =>
    simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
    cases orig with
    | ProgressiveZero =>
      simp [triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hrebase
      subst after
      exact .same _ _
    | ProgressiveNode origHash origLeft origRight =>
      cases base with
      | ProgressiveZero =>
        simp [triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hrebase
        subst after
        exact .same _ _
      | ProgressiveNode baseHash baseLeft baseRight =>
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨start, hstart, hrebase⟩ := hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨next, hnext, hrebase⟩ := hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨capacity, hcapacity, hrebase⟩ := hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨binary, hbinary, hrebase⟩ := hrebase
        simp only [hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq,
          lift, bind_tc_ok] at hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨origLeftLength, horigLength, hrebase⟩ := hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨baseLeftLength, hbaseLength, hrebase⟩ := hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨fullDepth, hfullDepth, hrebase⟩ := hrebase
        rw [bind_eq_ok_iff] at hrebase
        obtain ⟨leftResult, hleft, hrebase⟩ := hrebase
        cases leftResult with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hrebase
        | Ok action =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrebase
          rw [bind_eq_ok_iff] at hrebase
          obtain ⟨newLeft, hnewLeft, hrebase⟩ := hrebase
          have heq : newLeft = tree.applyRebaseAction origLeft action := by
            cases action <;> simpa [tree.applyRebaseAction,
              triomphe.arc.Arc.Insts.CoreCloneClone.clone] using hnewLeft.symm
          subst newLeft
          rw [bind_eq_ok_iff] at hrebase
          obtain ⟨rightResult, hright, hrebase⟩ := hrebase
          cases rightResult with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hrebase
          | Ok newRight =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrebase
            rw [bind_eq_ok_iff] at hrebase
            obtain ⟨leftSame, hleftSame, hrebase⟩ := hrebase
            have hnode : ProgressiveTree.RebaseStep ValueInst origLength baseLength depth packingDepth
                (.ProgressiveNode origHash origLeft origRight) (.ProgressiveNode baseHash baseLeft baseRight)
                (.ProgressiveNode origHash (tree.applyRebaseAction origLeft action) newRight) :=
              .node action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright
            cases leftSame with
            | false =>
              simp [lock_api.rwlock.RwLock.read,
                lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
                lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hrebase
              subst after
              exact hnode
            | true =>
              simp only [↓reduceIte] at hrebase
              rw [bind_eq_ok_iff] at hrebase
              obtain ⟨rightSame, hrightSame, hrebase⟩ := hrebase
              cases rightSame with
              | false =>
                simp [lock_api.rwlock.RwLock.read,
                  lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
                  lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hrebase
                subst after
                exact hnode
              | true =>
                simp [triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hrebase
                subst after
                exact .same _ _

end milhouse.progressive_tree
