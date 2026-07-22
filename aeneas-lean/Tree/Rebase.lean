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

/-- The `(depth, hash)` key used by `Tree.intra_rebase` cannot determine the
    represented dense length. The input below is dense with length three and
    contains a full left subtree and a partial right subtree under the same
    cached hash. Replacing the right subtree by the left one produces a
    length-four shape, which is not dense at the original length. -/
theorem intraRebaseKey_allows_length_changing_replacement {T : Type}
    (root_hash repeated_hash :
      alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (left_leaf right_leaf : leaf.Leaf T) :
    let full := Tree.Node repeated_hash (Tree.Leaf left_leaf)
      (Tree.Leaf right_leaf)
    let sparse := Tree.Node repeated_hash (Tree.Leaf left_leaf)
      (Tree.Zero 0#usize)
    DenseTree none (Tree.Node root_hash full sparse) 2 3 ∧
      ¬ DenseTree none (Tree.Node root_hash full full) 2 3 := by
  dsimp only
  have hfull : DenseTree none
      (Tree.Node repeated_hash (Tree.Leaf left_leaf)
        (Tree.Leaf right_leaf)) 1 2 := by
    exact DenseTree.node none repeated_hash (Tree.Leaf left_leaf)
      (Tree.Leaf right_leaf) 0 1 1 (DenseTree.leaf left_leaf)
      (DenseTree.leaf right_leaf) (by omega)
      (by simp [subtreeCapacity, leafCapacity])
  have hpartial : DenseTree none
      (Tree.Node repeated_hash (Tree.Leaf left_leaf)
        (Tree.Zero 0#usize)) 1 1 := by
    exact DenseTree.node none repeated_hash (Tree.Leaf left_leaf)
      (Tree.Zero 0#usize) 0 1 0 (DenseTree.leaf left_leaf)
      (DenseTree.zero none 0#usize) (by omega) (by omega)
  constructor
  · exact DenseTree.node none root_hash
      (Tree.Node repeated_hash (Tree.Leaf left_leaf) (Tree.Leaf right_leaf))
      (Tree.Node repeated_hash (Tree.Leaf left_leaf) (Tree.Zero 0#usize))
      1 2 1 hfull hpartial (by omega)
      (by simp [subtreeCapacity, leafCapacity])
  · intro hbad
    have hlength_four : DenseTree none
        (Tree.Node root_hash
          (Tree.Node repeated_hash (Tree.Leaf left_leaf)
            (Tree.Leaf right_leaf))
          (Tree.Node repeated_hash (Tree.Leaf left_leaf)
            (Tree.Leaf right_leaf))) 2 4 := by
      exact DenseTree.node none root_hash
        (Tree.Node repeated_hash (Tree.Leaf left_leaf) (Tree.Leaf right_leaf))
        (Tree.Node repeated_hash (Tree.Leaf left_leaf) (Tree.Leaf right_leaf))
        1 2 2 hfull hfull (by omega)
        (by simp [subtreeCapacity, leafCapacity])
    have hunique := DenseTree.indices_unique hbad hlength_four
    omega

end milhouse.tree
