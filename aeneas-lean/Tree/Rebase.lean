-- Density preservation machinery for structural sharing.
import Tree.Invariants
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open milhouse

namespace milhouse.tree

/-- A tree obtained by choosing corresponding pieces of two trees. This is
    the shape-level effect of `Tree.rebase_on`: cache hashes and ownership may
    change, but a replacement never moves a subtree to a different position. -/
inductive PositionalMix {T : Type} : Tree T → Tree T → Tree T → Prop where
  | orig (orig base : Tree T) : PositionalMix orig base orig
  | base (orig base : Tree T) : PositionalMix orig base base
  | node
      (orig_hash base_hash new_hash :
        alloy_primitives.bits.fixed.FixedBytes 32#usize)
      (orig_left orig_right base_left base_right new_left new_right : Tree T)
      (left_mix : PositionalMix orig_left base_left new_left)
      (right_mix : PositionalMix orig_right base_right new_right) :
      PositionalMix
        (Tree.Node orig_hash orig_left orig_right)
        (Tree.Node base_hash base_left base_right)
        (Tree.Node new_hash new_left new_right)

private theorem dense_split_unique {capacity left₁ right₁ left₂ right₂ : Nat}
    (left₁_bound : left₁ ≤ capacity)
    (left₂_bound : left₂ ≤ capacity)
    (left₁_nonempty : 0 < left₁)
    (left₂_nonempty : 0 < left₂)
    (left₁_full : 0 < right₁ → left₁ = capacity)
    (left₂_full : 0 < right₂ → left₂ = capacity)
    (length_eq : left₁ + right₁ = left₂ + right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  by_cases hright₁ : 0 < right₁ <;>
    by_cases hright₂ : 0 < right₂
  · have hfull₁ := left₁_full hright₁
    have hfull₂ := left₂_full hright₂
    omega
  · have hfull₁ := left₁_full hright₁
    omega
  · have hfull₂ := left₂_full hright₂
    omega
  · omega

private theorem dense_node_inv {T : Type}
    {packing_factor : Option Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    {left right : Tree T} {depth len : Nat}
    (h : DenseTree packing_factor (Tree.Node hash left right) depth len) :
    ∃ child_depth left_len right_len,
      depth = child_depth + 1 ∧ len = left_len + right_len ∧
      DenseTree packing_factor left child_depth left_len ∧
      DenseTree packing_factor right child_depth right_len ∧
      0 < left_len ∧
      (0 < right_len →
        left_len = subtreeCapacity packing_factor child_depth) := by
  cases h with
  | node _ _ _ _ child_depth left_len right_len hleft hright hleftpos hfull =>
    exact ⟨child_depth, left_len, right_len, rfl, rfl, hleft, hright,
      hleftpos, hfull⟩

/-- Mixing corresponding positions of two dense trees with the same logical
    indices produces another dense tree with those indices. -/
theorem PositionalMix.preserves_dense {T : Type}
    {packing_factor : Option Std.Usize} {orig base mixed : Tree T}
    {depth len : Nat}
    (hmix : PositionalMix orig base mixed)
    (horig : DenseTree packing_factor orig depth len)
    (hbase : DenseTree packing_factor base depth len) :
    DenseTree packing_factor mixed depth len := by
  induction hmix generalizing depth len with
  | orig orig base => exact horig
  | base orig base => exact hbase
  | node orig_hash base_hash new_hash orig_left orig_right base_left base_right
      new_left new_right left_mix right_mix ihleft ihright =>
    obtain ⟨orig_child_depth, orig_left_len, orig_right_len,
      horig_depth, horig_len, orig_left_dense, orig_right_dense,
      orig_left_nonempty, orig_left_full⟩ := dense_node_inv horig
    obtain ⟨base_child_depth, base_left_len, base_right_len,
      hbase_depth, hbase_len, base_left_dense, base_right_dense,
      base_left_nonempty, base_left_full⟩ := dense_node_inv hbase
    have hchild_depth : orig_child_depth = base_child_depth := by omega
    subst base_child_depth
    have hsplit := dense_split_unique
      orig_left_dense.length_le_capacity
      base_left_dense.length_le_capacity
      orig_left_nonempty base_left_nonempty orig_left_full base_left_full
      (by omega)
    obtain ⟨hleft_len, hright_len⟩ := hsplit
    subst base_left_len
    subst base_right_len
    rw [horig_depth, horig_len]
    exact DenseTree.node packing_factor new_hash new_left new_right
      orig_child_depth orig_left_len orig_right_len
      (ihleft orig_left_dense base_left_dense)
      (ihright orig_right_dense base_right_dense)
      orig_left_nonempty orig_left_full

/-- The concrete tree denoted by a rebase action: no-op actions retain the
    original, while replacement actions carry their new tree. -/
def applyRebaseAction {T : Type} (orig : Tree T) :
    tree.RebaseAction (Tree T) → Tree T
  | tree.RebaseAction.NotEqualNoop => orig
  | tree.RebaseAction.NotEqualReplace replacement => replacement
  | tree.RebaseAction.EqualNoop => orig
  | tree.RebaseAction.EqualReplace replacement => replacement

private def combineRebaseActions {T : Type}
    (orig_hash base_hash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (orig_left orig_right base_left base_right : Tree T)
    (left_action right_action : tree.RebaseAction (Tree T)) :
    tree.RebaseAction (Tree T) :=
  match left_action, right_action with
  | .NotEqualNoop, .NotEqualNoop => .NotEqualNoop
  | .NotEqualNoop, .NotEqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash orig_left new_right)
  | .NotEqualNoop, .EqualNoop => .NotEqualNoop
  | .NotEqualNoop, .EqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash orig_left new_right)
  | .NotEqualReplace new_left, .NotEqualNoop =>
      .NotEqualReplace (Tree.Node orig_hash new_left orig_right)
  | .NotEqualReplace new_left, .NotEqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash new_left new_right)
  | .NotEqualReplace new_left, .EqualNoop =>
      .NotEqualReplace (Tree.Node orig_hash new_left orig_right)
  | .NotEqualReplace new_left, .EqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash new_left new_right)
  | .EqualNoop, .NotEqualNoop => .NotEqualNoop
  | .EqualNoop, .NotEqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash orig_left new_right)
  | .EqualNoop, .EqualNoop => .EqualNoop
  | .EqualNoop, .EqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash orig_left new_right)
  | .EqualReplace new_left, .NotEqualNoop =>
      .NotEqualReplace (Tree.Node orig_hash new_left orig_right)
  | .EqualReplace new_left, .NotEqualReplace new_right =>
      .NotEqualReplace (Tree.Node orig_hash new_left new_right)
  | .EqualReplace _, .EqualNoop =>
      .EqualReplace (Tree.Node base_hash base_left base_right)
  | .EqualReplace _, .EqualReplace _ =>
      .EqualReplace (Tree.Node base_hash base_left base_right)

private theorem combineRebaseActions_is_positional {T : Type}
    (orig_hash base_hash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (orig_left orig_right base_left base_right : Tree T)
    (left_action right_action : tree.RebaseAction (Tree T))
    (hleft : PositionalMix orig_left base_left
      (applyRebaseAction orig_left left_action))
    (hright : PositionalMix orig_right base_right
      (applyRebaseAction orig_right right_action)) :
    PositionalMix
      (Tree.Node orig_hash orig_left orig_right)
      (Tree.Node base_hash base_left base_right)
      (applyRebaseAction (Tree.Node orig_hash orig_left orig_right)
        (combineRebaseActions orig_hash base_hash orig_left orig_right
          base_left base_right left_action right_action)) := by
  cases left_action <;> cases right_action <;>
    simp [applyRebaseAction, combineRebaseActions] at hleft hright ⊢
  all_goals first
    | exact PositionalMix.orig _ _
    | exact PositionalMix.base _ _
    | exact PositionalMix.node orig_hash base_hash orig_hash _ _ _ _ _ _
        hleft hright

private def rebaseChildren {T : Type} (ValueInst : Value T)
    (orig_hash base_hash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (orig_left orig_right base_left base_right : Tree T)
    (lengths : Option (utils.Length × utils.Length))
    (full_depth : Std.Usize) :
    Result (core.result.Result (tree.RebaseAction (Tree T)) error.Error) := do
  let new_depth ← full_depth - 1#usize
  let mapped ← core.option.Option.map
    (Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength
      ValueInst) lengths new_depth
  let (left_lengths, right_lengths) ← core.option.OptionPair.unzip mapped
  let left_result ←
    Tree.rebase_on ValueInst orig_left base_left left_lengths new_depth
  let left_flow ← core.result.Result.Insts.CoreOpsTry.branch left_result
  match left_flow with
  | core.ops.control_flow.ControlFlow.Continue left_action =>
    let right_result ←
      Tree.rebase_on ValueInst orig_right base_right right_lengths new_depth
    let right_flow ← core.result.Result.Insts.CoreOpsTry.branch right_result
    match right_flow with
    | core.ops.control_flow.ControlFlow.Continue right_action =>
      match left_action with
        | .NotEqualNoop => match right_action with
          | .NotEqualNoop => ok (core.result.Result.Ok .NotEqualNoop)
          | .NotEqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash orig_left new_right)))
          | .EqualNoop => ok (core.result.Result.Ok .NotEqualNoop)
          | .EqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash orig_left new_right)))
        | .NotEqualReplace new_left => match right_action with
          | .NotEqualNoop =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash new_left orig_right)))
          | .NotEqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash new_left new_right)))
          | .EqualNoop =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash new_left orig_right)))
          | .EqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash new_left new_right)))
        | .EqualNoop => match right_action with
          | .NotEqualNoop => ok (core.result.Result.Ok .NotEqualNoop)
          | .NotEqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash orig_left new_right)))
          | .EqualNoop => ok (core.result.Result.Ok .EqualNoop)
          | .EqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash orig_left new_right)))
        | .EqualReplace new_left => match right_action with
          | .NotEqualNoop =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash new_left orig_right)))
          | .NotEqualReplace new_right =>
              ok (core.result.Result.Ok (.NotEqualReplace
                (Tree.Node orig_hash new_left new_right)))
          | .EqualNoop =>
              ok (core.result.Result.Ok (.EqualReplace
                (Tree.Node base_hash base_left base_right)))
          | .EqualReplace _ =>
              ok (core.result.Result.Ok (.EqualReplace
                (Tree.Node base_hash base_left base_right)))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (tree.RebaseAction (Tree T)) (core.convert.FromSame error.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (tree.RebaseAction (Tree T)) (core.convert.FromSame error.Error) residual

private theorem try_branch_continue_eq {A E : Type}
    {result : core.result.Result A E} {value : A}
    (h : core.result.Result.Insts.CoreOpsTry.branch result =
      ok (core.ops.control_flow.ControlFlow.Continue value)) :
    result = core.result.Result.Ok value := by
  cases result with
  | Ok actual =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    exact congrArg core.result.Result.Ok h
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h

private theorem residual_cannot_return_ok {A E : Type}
    {residual : core.result.Result core.convert.Infallible E} {value : A}
    (h : core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      A (core.convert.FromSame E) residual =
      ok (core.result.Result.Ok value)) : False := by
  cases residual with
  | Ok impossible => exact nomatch impossible
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h

private theorem rebaseChildren_is_positional {T : Type} (ValueInst : Value T)
    (orig_hash base_hash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (orig_left orig_right base_left base_right : Tree T)
    (lengths : Option (utils.Length × utils.Length))
    (full_depth : Std.Usize) (action : tree.RebaseAction (Tree T))
    (hchildren : rebaseChildren ValueInst orig_hash base_hash orig_left
      orig_right base_left base_right lengths full_depth =
      ok (core.result.Result.Ok action))
    (hrecursive : ∀ (new_depth : Std.Usize),
      full_depth - 1#usize = ok new_depth →
      ∀ (orig base : Tree T)
        (child_lengths : Option (utils.Length × utils.Length))
        (child_action : tree.RebaseAction (Tree T)),
        Tree.rebase_on ValueInst orig base child_lengths new_depth =
          ok (core.result.Result.Ok child_action) →
        PositionalMix orig base (applyRebaseAction orig child_action)) :
    PositionalMix (Tree.Node orig_hash orig_left orig_right)
      (Tree.Node base_hash base_left base_right)
      (applyRebaseAction (Tree.Node orig_hash orig_left orig_right) action) := by
  unfold rebaseChildren at hchildren
  cases hnew_depth : full_depth - 1#usize with
  | fail e => rw [hnew_depth] at hchildren; simp at hchildren
  | div => rw [hnew_depth] at hchildren; simp at hchildren
  | ok new_depth =>
    rw [hnew_depth] at hchildren
    simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
    cases hmapped : core.option.Option.map
        (Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength
          ValueInst) lengths new_depth with
    | fail e => rw [hmapped] at hchildren; simp at hchildren
    | div => rw [hmapped] at hchildren; simp at hchildren
    | ok mapped =>
      rw [hmapped] at hchildren
      simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
      cases hunzip : core.option.OptionPair.unzip mapped with
      | fail e => rw [hunzip] at hchildren; simp at hchildren
      | div => rw [hunzip] at hchildren; simp at hchildren
      | ok split_lengths =>
        rw [hunzip] at hchildren
        simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
        obtain ⟨left_lengths, right_lengths⟩ := split_lengths
        simp at hchildren
        cases hleft_result : Tree.rebase_on ValueInst orig_left base_left
            left_lengths new_depth with
        | fail e => rw [hleft_result] at hchildren; simp at hchildren
        | div => rw [hleft_result] at hchildren; simp at hchildren
        | ok left_result =>
          rw [hleft_result] at hchildren
          simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
          cases hleft_flow : core.result.Result.Insts.CoreOpsTry.branch
              left_result with
          | fail e => rw [hleft_flow] at hchildren; simp at hchildren
          | div => rw [hleft_flow] at hchildren; simp at hchildren
          | ok left_flow =>
            rw [hleft_flow] at hchildren
            simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
            cases left_flow with
            | Break residual =>
              exact (residual_cannot_return_ok hchildren).elim
            | Continue left_action =>
              cases hright_result : Tree.rebase_on ValueInst orig_right
                  base_right right_lengths new_depth with
              | fail e => rw [hright_result] at hchildren; simp at hchildren
              | div => rw [hright_result] at hchildren; simp at hchildren
              | ok right_result =>
                rw [hright_result] at hchildren
                simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
                cases hright_flow : core.result.Result.Insts.CoreOpsTry.branch
                    right_result with
                | fail e => rw [hright_flow] at hchildren; simp at hchildren
                | div => rw [hright_flow] at hchildren; simp at hchildren
                | ok right_flow =>
                  rw [hright_flow] at hchildren
                  simp only [Bind.bind, Std.bind, bind_tc_ok] at hchildren
                  cases right_flow with
                  | Break residual =>
                    exact (residual_cannot_return_ok hchildren).elim
                  | Continue right_action =>
                    simp at hchildren
                    have hleft_action :
                        left_result = core.result.Result.Ok left_action := by
                      exact try_branch_continue_eq hleft_flow
                    have hright_action :
                        right_result = core.result.Result.Ok right_action := by
                      exact try_branch_continue_eq hright_flow
                    rw [hleft_action] at hleft_result
                    rw [hright_action] at hright_result
                    have hleft_mix := hrecursive new_depth hnew_depth
                      orig_left base_left left_lengths left_action hleft_result
                    have hright_mix := hrecursive new_depth hnew_depth
                      orig_right base_right right_lengths right_action
                      hright_result
                    cases left_action <;> cases right_action <;>
                      simp at hchildren <;> subst action <;>
                      simpa [combineRebaseActions] using
                        (combineRebaseActions_is_positional orig_hash base_hash
                          orig_left orig_right base_left base_right _ _
                          hleft_mix hright_mix)

private theorem rebaseChildren_is_positional_of_ih {T : Type}
    (ValueInst : Value T) (n : Nat)
    (ih : ∀ m < n,
      ∀ (orig base : Tree T)
        (lengths : Option (utils.Length × utils.Length))
        (full_depth : Std.Usize) (action : tree.RebaseAction (Tree T)),
        full_depth.val ≤ m →
        Tree.rebase_on ValueInst orig base lengths full_depth =
          ok (core.result.Result.Ok action) →
        PositionalMix orig base (applyRebaseAction orig action))
    (orig_hash base_hash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (orig_left orig_right base_left base_right : Tree T)
    (lengths : Option (utils.Length × utils.Length))
    (full_depth : Std.Usize) (action : tree.RebaseAction (Tree T))
    (hdepth : full_depth.val ≤ n)
    (hchildren : rebaseChildren ValueInst orig_hash base_hash orig_left
      orig_right base_left base_right lengths full_depth =
      ok (core.result.Result.Ok action)) :
    PositionalMix (Tree.Node orig_hash orig_left orig_right)
      (Tree.Node base_hash base_left base_right)
      (applyRebaseAction (Tree.Node orig_hash orig_left orig_right) action) := by
  apply rebaseChildren_is_positional ValueInst orig_hash base_hash orig_left
    orig_right base_left base_right lengths full_depth action hchildren
  intro new_depth hnew_depth child_orig child_base child_lengths child_action
    hchild
  have hsub := UScalar.sub_equiv full_depth 1#usize
  rw [hnew_depth] at hsub
  have hdepth_eq : full_depth.val = new_depth.val + 1 := by
    obtain ⟨-, hone, -⟩ := hsub
    scalar_tac
  have hlt : new_depth.val < n := by omega
  exact ih new_depth.val hlt child_orig child_base child_lengths new_depth
    child_action (Nat.le_refl _) hchild

private theorem rebase_on_is_positional_aux {T : Type} (ValueInst : Value T) :
    ∀ (n : Nat) (orig base : Tree T)
      (lengths : Option (utils.Length × utils.Length))
      (full_depth : Std.Usize) (action : tree.RebaseAction (Tree T)),
      full_depth.val ≤ n →
      Tree.rebase_on ValueInst orig base lengths full_depth =
        ok (core.result.Result.Ok action) →
      PositionalMix orig base (applyRebaseAction orig action) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro orig base lengths full_depth action hdepth hrebase
    unfold Tree.rebase_on at hrebase
    obtain ⟨pointer_equal, hpointer, hpointer_true⟩ :=
      triomphe.arc.Arc.ptr_eq_spec orig base
    rw [hpointer] at hrebase
    cases pointer_equal with
    | true =>
      simp at hrebase
      subst action
      exact PositionalMix.orig orig base
    | false =>
      simp only [Bind.bind, Std.bind, bind_tc_ok, reduceCtorEq, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases orig <;> cases base <;> simp only at hrebase
      case Leaf.Leaf orig_leaf base_leaf =>
        cases heq : triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq
            ValueInst.corecmpPartialEqInst orig_leaf.value base_leaf.value with
        | fail e => rw [heq] at hrebase; simp at hrebase
        | div => rw [heq] at hrebase; simp at hrebase
        | ok equal =>
          rw [heq] at hrebase
          cases equal <;> simp [applyRebaseAction] at hrebase ⊢
          · subst action; exact PositionalMix.orig _ _
          · subst action; exact PositionalMix.base _ _
      case PackedLeaf.PackedLeaf orig_leaf base_leaf =>
        cases heq : alloc.vec.partial_eq.PartialEqVec.eq
            ValueInst.corecmpPartialEqInst orig_leaf.values base_leaf.values with
        | fail e => rw [heq] at hrebase; simp at hrebase
        | div => rw [heq] at hrebase; simp at hrebase
        | ok equal =>
          rw [heq] at hrebase
          cases equal <;> simp [applyRebaseAction] at hrebase ⊢
          · subst action; exact PositionalMix.orig _ _
          · subst action; exact PositionalMix.base _ _
      case Zero.Zero orig_depth base_depth =>
        simp [lift] at hrebase
        split at hrebase
        · simp at hrebase
          subst action
          exact PositionalMix.base _ _
        · simp at hrebase
          subst action
          exact PositionalMix.orig _ _
      case Node.Node orig_hash orig_left orig_right base_hash base_left
          base_right =>
        by_cases hfull_depth : full_depth > 0#usize
        · rw [if_pos hfull_depth] at hrebase
          simp [lock_api.rwlock.RwLock.read,
            lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
            alloy_primitives.bits.fixed.FixedBytes.is_zero,
            alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
            lock_api.rwlock.RwLock.new,
            triomphe.arc.Arc.Insts.CoreCloneClone.clone,
            triomphe.arc.Arc.new] at hrebase
          split at hrebase
          · apply rebaseChildren_is_positional_of_ih ValueInst n ih orig_hash
              base_hash orig_left orig_right base_left base_right lengths
              full_depth action hdepth
            change rebaseChildren ValueInst orig_hash base_hash orig_left
              orig_right base_left base_right lengths full_depth =
              ok (core.result.Result.Ok action) at hrebase
            exact hrebase
          · split at hrebase
            · cases hlengths : core.option.Option.is_none_or
                  (Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool
                    ValueInst) lengths () with
              | fail e => rw [hlengths] at hrebase; simp at hrebase
              | div => rw [hlengths] at hrebase; simp at hrebase
              | ok lengths_equal =>
                rw [hlengths] at hrebase
                cases lengths_equal with
                | false =>
                  simp at hrebase
                  apply rebaseChildren_is_positional_of_ih ValueInst n ih
                    orig_hash base_hash orig_left orig_right base_left base_right
                    lengths full_depth action hdepth
                  change rebaseChildren ValueInst orig_hash base_hash orig_left
                    orig_right base_left base_right lengths full_depth =
                    ok (core.result.Result.Ok action) at hrebase
                  exact hrebase
                | true =>
                  simp at hrebase
                  subst action
                  exact PositionalMix.base _ _
            · apply rebaseChildren_is_positional_of_ih ValueInst n ih
                orig_hash base_hash orig_left orig_right base_left base_right
                lengths full_depth action hdepth
              change rebaseChildren ValueInst orig_hash base_hash orig_left
                orig_right base_left base_right lengths full_depth =
                ok (core.result.Result.Ok action) at hrebase
              exact hrebase
        · rw [if_neg hfull_depth] at hrebase
          simp at hrebase
      all_goals simp at hrebase
      all_goals subst action
      all_goals exact PositionalMix.orig _ _

/-- Every successful `Tree.rebase_on` action is a positional mix of its two
    inputs. -/
theorem rebase_on_is_positional {T : Type} (ValueInst : Value T)
    (orig base : Tree T) (lengths : Option (utils.Length × utils.Length))
    (full_depth : Std.Usize) (action : tree.RebaseAction (Tree T))
    (hrebase : Tree.rebase_on ValueInst orig base lengths full_depth =
      ok (core.result.Result.Ok action)) :
    PositionalMix orig base (applyRebaseAction orig action) :=
  rebase_on_is_positional_aux ValueInst full_depth.val orig base lengths
    full_depth action (Nat.le_refl _) hrebase

/-- Once a rebase action is known to be positional, density follows directly. -/
theorem rebaseAction_preserves_dense {T : Type}
    {packing_factor : Option Std.Usize} {orig base : Tree T}
    {depth len : Nat} {action : tree.RebaseAction (Tree T)}
    (hmix : PositionalMix orig base (applyRebaseAction orig action))
    (horig : DenseTree packing_factor orig depth len)
    (hbase : DenseTree packing_factor base depth len) :
    DenseTree packing_factor (applyRebaseAction orig action) depth len :=
  hmix.preserves_dense horig hbase

/-- A successful translated rebase preserves density when both input trees
    represent the same dense prefix. -/
theorem rebase_on_preserves_dense {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize} {orig base : Tree T}
    {depth len : Nat} {lengths : Option (utils.Length × utils.Length)}
    {full_depth : Std.Usize} {action : tree.RebaseAction (Tree T)}
    (horig : DenseTree packing_factor orig depth len)
    (hbase : DenseTree packing_factor base depth len)
    (hrebase : Tree.rebase_on ValueInst orig base lengths full_depth =
      ok (core.result.Result.Ok action)) :
    DenseTree packing_factor (applyRebaseAction orig action) depth len :=
  (rebase_on_is_positional ValueInst orig base lengths full_depth action
    hrebase).preserves_dense horig hbase

/-! ## Intra-rebase preservation

`Tree.intra_rebase` deduplicates equal subtrees within a single tree, keyed
by `(depth, hash)`. A cached hash cannot distinguish virtual `Zero` padding
from materialized zero values, so hash equality alone does not determine the
represented dense length. The implementation therefore plumbs the
represented length top-down (mirroring `rebase_on`) and only stores and
replaces subtrees whose represented length equals their capacity. Two full
dense subtrees at equal depth represent equal lengths, so a replacement can
never change the dense prefix. In a dense tree this restriction forgoes
nothing: at most one subtree per depth is partial, so a partial subtree
never has an identically-positioned duplicate to share with. -/

/-- The `known_subtrees` map threaded through `Tree.intra_rebase`. -/
abbrev IntraRebaseMap (T : Type) :=
  std.collections.hash.map.HashMap
    (Std.Usize × alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (triomphe.arc.Arc (Tree T)) std.hash.random.RandomState Global

/-- The concrete tree denoted by an intra-rebase action. -/
def applyIntraRebaseAction {T : Type} (orig : Tree T) :
    tree.IntraRebaseAction (Tree T) → Tree T
  | tree.IntraRebaseAction.Noop => orig
  | tree.IntraRebaseAction.Replace replacement => replacement

/-- Invariant of the `known_subtrees` map: every stored subtree is dense and
    full at its keyed depth. -/
def FullDenseMap {T : Type} (packing_factor : Option Std.Usize)
    (map : IntraRebaseMap T) : Prop :=
  ∀ key subtree, (key, subtree) ∈ map →
    DenseTree packing_factor subtree key.1.val
      (subtreeCapacity packing_factor key.1.val)

/-- The empty map of the top-level `intra_rebase` call satisfies the
    invariant. -/
theorem FullDenseMap.empty {T : Type} (packing_factor : Option Std.Usize) :
    FullDenseMap (T := T) packing_factor [] := by
  intro key subtree hmem
  simp at hmem

/-! ### Arithmetic bridges -/

private theorem result_bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private theorem usize_add_val {x y sum : Std.Usize}
    (h : x + y = ok sum) : sum.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  rw [h] at hadd
  simp at hadd
  omega

private theorem usize_sub_one_val {x predecessor : Std.Usize}
    (h : x - 1#usize = ok predecessor) :
    x.val = predecessor.val + 1 := by
  have hsub := UScalar.sub_equiv x 1#usize
  rw [h] at hsub
  obtain ⟨-, hone, -⟩ := hsub
  scalar_tac

private theorem usize_sub_val {x y difference : Std.Usize}
    (h : x - y = ok difference) :
    difference.val = x.val - y.val := by
  have hsub := UScalar.sub_equiv x y
  rw [h] at hsub
  obtain ⟨-, heq, -⟩ := hsub
  omega

/-- A successful `1 << shift` is exactly the power of two. -/
private theorem usize_shift_left_one_val {shift shifted : Std.Usize}
    (h : 1#usize <<< shift = ok shifted) :
    shifted.val = 2 ^ shift.val := by
  have hbound : shift.val < UScalarTy.Usize.numBits := by
    change UScalar.shiftLeft 1#usize shift.val = ok shifted at h
    unfold UScalar.shiftLeft at h
    split at h
    · assumption
    · simp at h
  have hspec := UScalar.ShiftLeft_spec 1#usize shift
    (UScalar.size UScalarTy.Usize) hbound rfl
  rw [h] at hspec
  obtain ⟨hval, -⟩ := hspec
  have hone : (1#usize).val = 1 := by simp
  rw [hval, hone, Nat.one_shiftLeft, UScalar.size_def]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hbound)

/-- The translated `core::cmp::min` on `Length` is the natural-number
    minimum. -/
private theorem length_min_val {x y minimum : utils.Length}
    (h : core.cmp.min utils.Length.Insts.CoreCmpOrd x y = ok minimum) :
    (minimum.val = x.val ∧ x.val ≤ y.val) ∨
      (minimum.val = y.val ∧ y.val ≤ x.val) := by
  simp only [core.cmp.min, utils.Length.Insts.CoreCmpOrd,
    core.cmp.Ord.min_body, core.cmp.PartialOrd.lt_body,
    utils.Length.Insts.CoreCmpPartialOrdLength,
    utils.Length.Insts.CoreCmpPartialOrdLength.partial_cmp,
    utils.Length.Insts.CoreCmpOrd.cmp, core.cmp.impls.OrdUsize.cmp,
    Bind.bind, Std.bind] at h
  split at h <;> simp_all <;> subst minimum <;>
    (simp_all [Nat.compare_eq_lt]; try omega)

/-! ### Association-list model of `known_subtrees` -/

private theorem blanket_borrow_spec {K : Type} (k : K) :
    (core.borrow.Borrow.Blanket K).borrow k = ok k := by
  simp [core.borrow.Borrow.Blanket, core.borrow.Borrow.Blanket.borrow]

/-- The composite key comparison used by the intra-rebase map decides
    equality of `(depth, hash)` keys. -/
private theorem intra_key_eq_spec
    (k q : Std.Usize × alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    ∃ b, (Pair.Insts.CoreCmpEq core.cmp.EqUsize
        (alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpEq
          32#usize)).partialEqInst.eq k q = ok b ∧ (b = true ↔ k = q) := by
  obtain ⟨kd, kh⟩ := k
  obtain ⟨qd, qh⟩ := q
  simp only [Pair.Insts.CoreCmpEq, Pair.Insts.CoreCmpPartialEqPair,
    Pair.Insts.CoreCmpPartialEqPair.eq,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpEq,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
    core.cmp.EqUsize, core.cmp.PartialEqUsize,
    core.cmp.impls.PartialEqUsize.eq, liftFun2, bind_tc_ok]
  by_cases hd : kd = qd
  · by_cases hh : kh = qh
    · subst hd
      subst hh
      exact ⟨true, by simp, by simp⟩
    · have hval : ¬ kh.val = qh.val := fun hval => hh (Subtype.ext hval)
      exact ⟨false, by simp [hd, hval], by simp [hh]⟩
  · exact ⟨false, by simp [hd], by simp [hd]⟩

/-- Association-list lookup only returns entries of the list, at the queried
    key. -/
private theorem lookup_eq_some_mem {K V : Type}
    {borrow : K → Result K} {eq : K → K → Result Bool}
    (hborrow : ∀ k, borrow k = ok k)
    (heq : ∀ k q, ∃ b, eq k q = ok b ∧ (b = true ↔ k = q))
    {entries : List (K × V)} {q : K} {v : V}
    (h : TreeAux.lookup borrow eq entries q = ok (some v)) :
    (q, v) ∈ entries := by
  induction entries with
  | nil => simp [TreeAux.lookup] at h
  | cons entry rest ih =>
    obtain ⟨k, v'⟩ := entry
    obtain ⟨b, heqb, hiff⟩ := heq k q
    simp only [TreeAux.lookup, hborrow, heqb, bind_tc_ok] at h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      exact List.mem_cons_of_mem _ (ih h)
    | true =>
      simp only [if_true] at h
      have hv : v' = v := by simpa using h
      have hk : k = q := hiff.mp rfl
      subst hv
      subst hk
      exact List.mem_cons_self ..

/-- Association-list insertion only adds the inserted binding; every other
    entry of the result was already present. -/
private theorem insert_entries_subset {K V : Type}
    {eq : K → K → Result Bool}
    (heq : ∀ k q, ∃ b, eq k q = ok b ∧ (b = true ↔ k = q)) :
    ∀ {entries : List (K × V)} {k : K} {v : V} {previous : Option V}
      {updated : List (K × V)},
      TreeAux.insert eq entries k v = ok (previous, updated) →
      ∀ key value, (key, value) ∈ updated →
        (key = k ∧ value = v) ∨ (key, value) ∈ entries := by
  intro entries
  induction entries with
  | nil =>
    intro k v previous updated h key value hmem
    simp only [TreeAux.insert, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp at hmem
    exact Or.inl hmem
  | cons entry rest ih =>
    intro k v previous updated h key value hmem
    obtain ⟨k', v'⟩ := entry
    obtain ⟨b, heqb, hiff⟩ := heq k' k
    simp only [TreeAux.insert, heqb, bind_tc_ok] at h
    cases b with
    | true =>
      have hk : k' = k := hiff.mp rfl
      simp only [if_true, ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rcases List.mem_cons.mp hmem with hhead | htail
      · simp only [Prod.mk.injEq] at hhead
        exact Or.inl ⟨hhead.1.trans hk, hhead.2⟩
      · exact Or.inr (List.mem_cons_of_mem _ htail)
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      rw [result_bind_eq_ok_iff] at h
      obtain ⟨⟨o, rest'⟩, hrec, h⟩ := h
      simp at h
      obtain ⟨-, rfl⟩ := h
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact Or.inr (by rw [hhead]; exact List.mem_cons_self ..)
      · rcases ih hrec key value htail with hnew | hold
        · exact Or.inl hnew
        · exact Or.inr (List.mem_cons_of_mem _ hold)

/-! ### Preservation -/

private theorem intra_rebase_preserves_dense_aux {T : Type}
    (ValueInst : Value T) {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth) :
    ∀ (n : Nat) (orig : Tree T) (known_subtrees : IntraRebaseMap T)
      (current_depth : Std.Usize) (len : utils.Length)
      (action : tree.IntraRebaseAction (Tree T))
      (updated_map : IntraRebaseMap T),
      current_depth.val ≤ n →
      DenseTree packing_factor orig current_depth.val len.val →
      FullDenseMap packing_factor known_subtrees →
      Tree.intra_rebase ValueInst orig known_subtrees current_depth
        packing_depth len = ok (core.result.Result.Ok action, updated_map) →
      DenseTree packing_factor (applyIntraRebaseAction orig action)
        current_depth.val len.val ∧
        FullDenseMap packing_factor updated_map := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro orig known_subtrees current_depth len action updated_map hdepth
      hdense hmap hrebase
    unfold Tree.intra_rebase at hrebase
    simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
      bind_tc_ok] at hrebase
    cases orig with
    | Leaf l =>
      simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq]
        at hrebase
      obtain ⟨rfl, rfl⟩ := hrebase
      exact ⟨hdense, hmap⟩
    | PackedLeaf pl =>
      simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq]
        at hrebase
      obtain ⟨rfl, rfl⟩ := hrebase
      exact ⟨hdense, hmap⟩
    | Zero z =>
      simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq]
        at hrebase
      obtain ⟨rfl, rfl⟩ := hrebase
      exact ⟨hdense, hmap⟩
    | Node hash left right =>
      obtain ⟨child_depth, left_n, right_n, hdepth_eq, hlen_eq, hleft_dense,
        hright_dense, hleft_pos, hleft_full⟩ := dense_node_inv hdense
      have hpos : current_depth > 0#usize := by scalar_tac
      simp only [lock_api.rwlock.RwLock.read,
        lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
        alloy_primitives.bits.fixed.FixedBytes.is_zero,
        utils.Length.as_usize,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone,
        Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new,
        bind_tc_ok] at hrebase
      rw [if_pos hpos] at hrebase
      split at hrebase
      · simp at hrebase
      rw [result_bind_eq_ok_iff] at hrebase
      obtain ⟨i, hi, hrebase⟩ := hrebase
      have hi_val := usize_add_val hi
      rw [result_bind_eq_ok_iff] at hrebase
      obtain ⟨capacity, hcap, hrebase⟩ := hrebase
      have hcap_val := usize_shift_left_one_val hcap
      have hcap_parent : capacity.val =
          subtreeCapacity packing_factor current_depth.val := by
        rw [PackingLayout.subtreeCapacity_eq_two_pow hlayout, hcap_val, hi_val,
          Nat.add_comm]
      by_cases hfull : len = capacity
      · -- The subtree is full: consult and possibly extend the map.
        rw [if_pos hfull] at hrebase
        have hlen_cap : len.val =
            subtreeCapacity packing_factor current_depth.val := by
          rw [← hcap_parent, hfull]
        simp only [std.collections.hash.map.HashMap.get] at hrebase
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨cached, hlookup, hrebase⟩ := hrebase
        cases cached with
        | some known_subtree =>
          simp at hrebase
          obtain ⟨rfl, rfl⟩ := hrebase
          have hmem := lookup_eq_some_mem blanket_borrow_spec
            intra_key_eq_spec hlookup
          have hknown := hmap _ _ hmem
          refine ⟨?_, hmap⟩
          simpa [applyIntraRebaseAction, hlen_cap] using hknown
        | none =>
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨i2, hi2, hrebase⟩ := hrebase
          have hi2_val := usize_sub_one_val hi2
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨i3, hi3, hrebase⟩ := hrebase
          have hi3_val := usize_add_val hi3
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨child_capacity, hcc, hrebase⟩ := hrebase
          have hcc_val := usize_shift_left_one_val hcc
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨left_len, hmin, hrebase⟩ := hrebase
          have hmin_val := length_min_val hmin
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨i5, hi5, hrebase⟩ := hrebase
          have hi5_val := usize_sub_val hi5
          have hchild : child_depth = i2.val := by omega
          subst hchild
          have hcc_cap : child_capacity.val =
              subtreeCapacity packing_factor i2.val := by
            rw [PackingLayout.subtreeCapacity_eq_two_pow hlayout, hcc_val,
              hi3_val, Nat.add_comm]
          have hleft_cap := hleft_dense.length_le_capacity
          have hleft_len_val : left_len.val = left_n := by
            rcases Nat.eq_zero_or_pos right_n with hr0 | hrpos
            · rcases hmin_val with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
            · have hfull_left := hleft_full hrpos
              rcases hmin_val with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          have hi5_len_val : i5.val = right_n := by omega
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨⟨left_result, known1⟩, hrec_left, hrebase⟩ := hrebase
          simp at hrebase
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨left_flow, hbranch_left, hrebase⟩ := hrebase
          cases left_flow with
          | Break residual =>
            simp at hrebase
            rw [result_bind_eq_ok_iff] at hrebase
            obtain ⟨r2, hres, hrebase⟩ := hrebase
            simp only [ok.injEq, Prod.mk.injEq] at hrebase
            obtain ⟨rfl, -⟩ := hrebase
            exact (residual_cannot_return_ok hres).elim
          | Continue left_action =>
            simp at hrebase
            have hleft_ok := try_branch_continue_eq hbranch_left
            subst hleft_ok
            have hleft_dense' : DenseTree packing_factor left i2.val
                left_len.val := by rwa [hleft_len_val]
            obtain ⟨hleft_pres, hmap1⟩ := ih i2.val (by omega) left
              known_subtrees i2 left_len left_action known1 (Nat.le_refl _)
              hleft_dense' hmap hrec_left
            rw [result_bind_eq_ok_iff] at hrebase
            obtain ⟨⟨right_result, known2⟩, hrec_right, hrebase⟩ := hrebase
            simp at hrebase
            rw [result_bind_eq_ok_iff] at hrebase
            obtain ⟨right_flow, hbranch_right, hrebase⟩ := hrebase
            cases right_flow with
            | Break residual =>
              simp at hrebase
              rw [result_bind_eq_ok_iff] at hrebase
              obtain ⟨r2, hres, hrebase⟩ := hrebase
              simp only [ok.injEq, Prod.mk.injEq] at hrebase
              obtain ⟨rfl, -⟩ := hrebase
              exact (residual_cannot_return_ok hres).elim
            | Continue right_action =>
              simp at hrebase
              have hright_ok := try_branch_continue_eq hbranch_right
              subst hright_ok
              have hright_dense' : DenseTree packing_factor right i2.val
                  i5.val := by rwa [hi5_len_val]
              obtain ⟨hright_pres, hmap2⟩ := ih i2.val (by omega) right known1
                i2 i5 right_action known2 (Nat.le_refl _) hright_dense' hmap1
                hrec_right
              have hdepth_val : current_depth.val = i2.val + 1 := hi2_val
              have hlen_val : len.val = left_len.val + i5.val := by omega
              have hside_pos : 0 < left_len.val := by omega
              have hside_full : 0 < i5.val →
                  left_len.val = subtreeCapacity packing_factor i2.val := by
                intro hpos5
                have := hleft_full (by omega)
                omega
              cases left_action with
              | Noop =>
                cases right_action with
                | Noop =>
                  simp [std.collections.hash.map.HashMap.insert] at hrebase
                  rw [result_bind_eq_ok_iff] at hrebase
                  obtain ⟨⟨existing, known3⟩, hins, hrebase⟩ := hrebase
                  cases existing with
                  | some prev => simp [core.option.Option.is_some] at hrebase
                  | none =>
                    simp [core.option.Option.is_some] at hrebase
                    obtain ⟨rfl, rfl⟩ := hrebase
                    refine ⟨hdense, ?_⟩
                    intro key subtree hmem
                    rcases insert_entries_subset intra_key_eq_spec hins key
                      subtree hmem with ⟨rfl, rfl⟩ | hold
                    · simpa [← hlen_cap] using hdense
                    · exact hmap2 key subtree hold
                | Replace new_right =>
                  simp [std.collections.hash.map.HashMap.insert] at hrebase
                  rw [result_bind_eq_ok_iff] at hrebase
                  obtain ⟨⟨existing, known3⟩, hins, hrebase⟩ := hrebase
                  cases existing with
                  | some prev => simp [core.option.Option.is_some] at hrebase
                  | none =>
                    simp [core.option.Option.is_some] at hrebase
                    obtain ⟨rfl, rfl⟩ := hrebase
                    have hnr : DenseTree packing_factor new_right i2.val
                        i5.val := by
                      simpa [applyIntraRebaseAction] using hright_pres
                    have hnew_dense : DenseTree packing_factor
                        (Tree.Node hash left new_right) current_depth.val
                        len.val := by
                      rw [hdepth_val, hlen_val]
                      exact DenseTree.node packing_factor hash left new_right
                        i2.val left_len.val i5.val hleft_dense' hnr hside_pos
                        hside_full
                    refine ⟨by simpa [applyIntraRebaseAction] using hnew_dense,
                      ?_⟩
                    intro key subtree hmem
                    rcases insert_entries_subset intra_key_eq_spec hins key
                      subtree hmem with ⟨rfl, rfl⟩ | hold
                    · simpa [← hlen_cap] using hnew_dense
                    · exact hmap2 key subtree hold
              | Replace new_left =>
                have hnl : DenseTree packing_factor new_left i2.val
                    left_len.val := by
                  simpa [applyIntraRebaseAction] using hleft_pres
                cases right_action with
                | Noop =>
                  simp [std.collections.hash.map.HashMap.insert] at hrebase
                  rw [result_bind_eq_ok_iff] at hrebase
                  obtain ⟨⟨existing, known3⟩, hins, hrebase⟩ := hrebase
                  cases existing with
                  | some prev => simp [core.option.Option.is_some] at hrebase
                  | none =>
                    simp [core.option.Option.is_some] at hrebase
                    obtain ⟨rfl, rfl⟩ := hrebase
                    have hnew_dense : DenseTree packing_factor
                        (Tree.Node hash new_left right) current_depth.val
                        len.val := by
                      rw [hdepth_val, hlen_val]
                      exact DenseTree.node packing_factor hash new_left right
                        i2.val left_len.val i5.val hnl hright_dense' hside_pos
                        hside_full
                    refine ⟨by simpa [applyIntraRebaseAction] using hnew_dense,
                      ?_⟩
                    intro key subtree hmem
                    rcases insert_entries_subset intra_key_eq_spec hins key
                      subtree hmem with ⟨rfl, rfl⟩ | hold
                    · simpa [← hlen_cap] using hnew_dense
                    · exact hmap2 key subtree hold
                | Replace new_right =>
                  simp [std.collections.hash.map.HashMap.insert] at hrebase
                  rw [result_bind_eq_ok_iff] at hrebase
                  obtain ⟨⟨existing, known3⟩, hins, hrebase⟩ := hrebase
                  cases existing with
                  | some prev => simp [core.option.Option.is_some] at hrebase
                  | none =>
                    simp [core.option.Option.is_some] at hrebase
                    obtain ⟨rfl, rfl⟩ := hrebase
                    have hnr : DenseTree packing_factor new_right i2.val
                        i5.val := by
                      simpa [applyIntraRebaseAction] using hright_pres
                    have hnew_dense : DenseTree packing_factor
                        (Tree.Node hash new_left new_right) current_depth.val
                        len.val := by
                      rw [hdepth_val, hlen_val]
                      exact DenseTree.node packing_factor hash new_left
                        new_right i2.val left_len.val i5.val hnl hnr hside_pos
                        hside_full
                    refine ⟨by simpa [applyIntraRebaseAction] using hnew_dense,
                      ?_⟩
                    intro key subtree hmem
                    rcases insert_entries_subset intra_key_eq_spec hins key
                      subtree hmem with ⟨rfl, rfl⟩ | hold
                    · simpa [← hlen_cap] using hnew_dense
                    · exact hmap2 key subtree hold
      · -- The subtree is partial: recurse without touching the map.
        rw [if_neg hfull] at hrebase
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨i2, hi2, hrebase⟩ := hrebase
        have hi2_val := usize_sub_one_val hi2
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨i3, hi3, hrebase⟩ := hrebase
        have hi3_val := usize_add_val hi3
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨child_capacity, hcc, hrebase⟩ := hrebase
        have hcc_val := usize_shift_left_one_val hcc
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨left_len, hmin, hrebase⟩ := hrebase
        have hmin_val := length_min_val hmin
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨i5, hi5, hrebase⟩ := hrebase
        have hi5_val := usize_sub_val hi5
        have hchild : child_depth = i2.val := by omega
        subst hchild
        have hcc_cap : child_capacity.val =
            subtreeCapacity packing_factor i2.val := by
          rw [PackingLayout.subtreeCapacity_eq_two_pow hlayout, hcc_val,
            hi3_val, Nat.add_comm]
        have hleft_cap := hleft_dense.length_le_capacity
        have hleft_len_val : left_len.val = left_n := by
          rcases Nat.eq_zero_or_pos right_n with hr0 | hrpos
          · rcases hmin_val with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          · have hfull_left := hleft_full hrpos
            rcases hmin_val with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        have hi5_len_val : i5.val = right_n := by omega
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨⟨left_result, known1⟩, hrec_left, hrebase⟩ := hrebase
        simp at hrebase
        rw [result_bind_eq_ok_iff] at hrebase
        obtain ⟨left_flow, hbranch_left, hrebase⟩ := hrebase
        cases left_flow with
        | Break residual =>
          simp at hrebase
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨r2, hres, hrebase⟩ := hrebase
          simp only [ok.injEq, Prod.mk.injEq] at hrebase
          obtain ⟨rfl, -⟩ := hrebase
          exact (residual_cannot_return_ok hres).elim
        | Continue left_action =>
          simp at hrebase
          have hleft_ok := try_branch_continue_eq hbranch_left
          subst hleft_ok
          have hleft_dense' : DenseTree packing_factor left i2.val
              left_len.val := by rwa [hleft_len_val]
          obtain ⟨hleft_pres, hmap1⟩ := ih i2.val (by omega) left
            known_subtrees i2 left_len left_action known1 (Nat.le_refl _)
            hleft_dense' hmap hrec_left
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨⟨right_result, known2⟩, hrec_right, hrebase⟩ := hrebase
          simp at hrebase
          rw [result_bind_eq_ok_iff] at hrebase
          obtain ⟨right_flow, hbranch_right, hrebase⟩ := hrebase
          cases right_flow with
          | Break residual =>
            simp at hrebase
            rw [result_bind_eq_ok_iff] at hrebase
            obtain ⟨r2, hres, hrebase⟩ := hrebase
            simp only [ok.injEq, Prod.mk.injEq] at hrebase
            obtain ⟨rfl, -⟩ := hrebase
            exact (residual_cannot_return_ok hres).elim
          | Continue right_action =>
            simp at hrebase
            have hright_ok := try_branch_continue_eq hbranch_right
            subst hright_ok
            have hright_dense' : DenseTree packing_factor right i2.val
                i5.val := by rwa [hi5_len_val]
            obtain ⟨hright_pres, hmap2⟩ := ih i2.val (by omega) right known1
              i2 i5 right_action known2 (Nat.le_refl _) hright_dense' hmap1
              hrec_right
            have hdepth_val : current_depth.val = i2.val + 1 := hi2_val
            have hlen_val : len.val = left_len.val + i5.val := by omega
            have hside_pos : 0 < left_len.val := by omega
            have hside_full : 0 < i5.val →
                left_len.val = subtreeCapacity packing_factor i2.val := by
              intro hpos5
              have := hleft_full (by omega)
              omega
            cases left_action with
            | Noop =>
              cases right_action with
              | Noop =>
                simp at hrebase
                obtain ⟨rfl, rfl⟩ := hrebase
                exact ⟨hdense, hmap2⟩
              | Replace new_right =>
                simp at hrebase
                obtain ⟨rfl, rfl⟩ := hrebase
                have hnr : DenseTree packing_factor new_right i2.val
                    i5.val := by
                  simpa [applyIntraRebaseAction] using hright_pres
                refine ⟨?_, hmap2⟩
                have hnew_dense : DenseTree packing_factor
                    (Tree.Node hash left new_right) current_depth.val
                    len.val := by
                  rw [hdepth_val, hlen_val]
                  exact DenseTree.node packing_factor hash left new_right
                    i2.val left_len.val i5.val hleft_dense' hnr hside_pos
                    hside_full
                simpa [applyIntraRebaseAction] using hnew_dense
            | Replace new_left =>
              have hnl : DenseTree packing_factor new_left i2.val
                  left_len.val := by
                simpa [applyIntraRebaseAction] using hleft_pres
              cases right_action with
              | Noop =>
                simp at hrebase
                obtain ⟨rfl, rfl⟩ := hrebase
                refine ⟨?_, hmap2⟩
                have hnew_dense : DenseTree packing_factor
                    (Tree.Node hash new_left right) current_depth.val
                    len.val := by
                  rw [hdepth_val, hlen_val]
                  exact DenseTree.node packing_factor hash new_left right
                    i2.val left_len.val i5.val hnl hright_dense' hside_pos
                    hside_full
                simpa [applyIntraRebaseAction] using hnew_dense
              | Replace new_right =>
                simp at hrebase
                obtain ⟨rfl, rfl⟩ := hrebase
                have hnr : DenseTree packing_factor new_right i2.val
                    i5.val := by
                  simpa [applyIntraRebaseAction] using hright_pres
                refine ⟨?_, hmap2⟩
                have hnew_dense : DenseTree packing_factor
                    (Tree.Node hash new_left new_right) current_depth.val
                    len.val := by
                  rw [hdepth_val, hlen_val]
                  exact DenseTree.node packing_factor hash new_left new_right
                    i2.val left_len.val i5.val hnl hnr hside_pos hside_full
                simpa [applyIntraRebaseAction] using hnew_dense

/-- A successful translated intra-rebase preserves density: replacements are
    drawn only from the full-subtree map, so the represented dense prefix is
    unchanged. -/
theorem intra_rebase_preserves_dense {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    {orig : Tree T} {known_subtrees updated_map : IntraRebaseMap T}
    {current_depth : Std.Usize} {len : utils.Length}
    {action : tree.IntraRebaseAction (Tree T)}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor orig current_depth.val len.val)
    (hmap : FullDenseMap packing_factor known_subtrees)
    (hrebase : Tree.intra_rebase ValueInst orig known_subtrees current_depth
      packing_depth len = ok (core.result.Result.Ok action, updated_map)) :
    DenseTree packing_factor (applyIntraRebaseAction orig action)
      current_depth.val len.val ∧
      FullDenseMap packing_factor updated_map :=
  intra_rebase_preserves_dense_aux ValueInst hlayout current_depth.val orig
    known_subtrees current_depth len action updated_map (Nat.le_refl _)
    hdense hmap hrebase

/-- Density preservation for the top-level intra-rebase call: starting from
    the empty `known_subtrees` map, no premise about the map is needed. -/
theorem intra_rebase_empty_preserves_dense {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    {orig : Tree T} {updated_map : IntraRebaseMap T}
    {current_depth : Std.Usize} {len : utils.Length}
    {action : tree.IntraRebaseAction (Tree T)}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor orig current_depth.val len.val)
    (hrebase : Tree.intra_rebase ValueInst orig [] current_depth
      packing_depth len = ok (core.result.Result.Ok action, updated_map)) :
    DenseTree packing_factor (applyIntraRebaseAction orig action)
      current_depth.val len.val :=
  (intra_rebase_preserves_dense ValueInst hlayout hdense
    (FullDenseMap.empty packing_factor) hrebase).1

end milhouse.tree
