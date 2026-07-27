-- Builder stack invariants and preservation.
import Tree.Invariants

open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Builder stack shape -/

/-- The tree represented by a builder stack entry. `Arc` is erased by the
    functional translation, so both variants have the same logical payload. -/
def maybeArcedTree {T : Type} : utils.MaybeArced (Tree T) → Tree T
  | .Arced tree => tree
  | .Unarced tree => tree

@[simp] theorem maybeArcedTree_arced {T : Type} (tree : Tree T) :
    maybeArcedTree (utils.MaybeArced.Arced tree) = tree := rfl

@[simp] theorem maybeArcedTree_unarced {T : Type} (tree : Tree T) :
    maybeArcedTree (utils.MaybeArced.Unarced tree) = tree := rfl

@[simp]
theorem maybeArced_arced {T : Type} (entry : utils.MaybeArced (Tree T)) :
    utils.MaybeArced.arced entry = ok (maybeArcedTree entry) := by
  cases entry <;> rfl

/-- A builder stack is the canonical left-to-right decomposition of a dense
    prefix at a fixed root depth.

    At depth zero the stack contains its one (possibly partial) leaf. At an
    internal level, the prefix either lies wholly in the left child, or the
    stack starts with a full left child followed by the canonical stack for a
    nonempty prefix of the right child. This formulation captures both the
    binary-counter stack used by `push` and the subtree stack used by
    `push_node`, without exposing either operation's loop counters. -/
inductive BuilderStack {T : Type} (packing_factor : Option Std.Usize) :
    List (utils.MaybeArced (Tree T)) → Nat → Nat → Prop where
  | empty (depth : Nat) : BuilderStack packing_factor [] depth 0
  | base (entry : utils.MaybeArced (Tree T)) (len : Nat)
      (dense : DenseTree packing_factor (maybeArcedTree entry) 0 len)
      (nonempty : 0 < len) :
      BuilderStack packing_factor [entry] 0 len
  | left {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
      (child_prefix : BuilderStack packing_factor stack depth len)
      (fits_left : len ≤ subtreeCapacity packing_factor depth) :
      BuilderStack packing_factor stack (depth + 1) len
  | right (left : utils.MaybeArced (Tree T))
      {right_stack : List (utils.MaybeArced (Tree T))}
      (depth right_len : Nat)
      (left_dense : DenseTree packing_factor (maybeArcedTree left) depth
        (subtreeCapacity packing_factor depth))
      (right_prefix : BuilderStack packing_factor right_stack depth right_len)
      (right_nonempty : 0 < right_len) :
      BuilderStack packing_factor (left :: right_stack) (depth + 1)
        (subtreeCapacity packing_factor depth + right_len)

theorem BuilderStack.length_le_capacity {T : Type}
    {packing_factor : Option Std.Usize}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor stack depth len) :
    len ≤ subtreeCapacity packing_factor depth := by
  induction h with
  | empty => simp
  | base entry len dense nonempty => exact dense.length_le_capacity
  | @left stack child_depth child_len child_prefix fits_left ih =>
    have hcap : subtreeCapacity packing_factor (child_depth + 1) =
        2 * subtreeCapacity packing_factor child_depth := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
    rw [hcap]
    omega
  | @right left right_stack child_depth right_len left_dense right_prefix
      right_nonempty ih =>
    have hcap : subtreeCapacity packing_factor (child_depth + 1) =
        2 * subtreeCapacity packing_factor child_depth := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
    rw [hcap]
    have hright := ih
    omega

/-- The translated builder fields agree with its packing layout and its stack
    is the canonical decomposition of the reported dense prefix. The level
    restriction records the two modes created inside this crate: leaf level
    zero, or a level at/above the packing boundary. -/
structure BuilderInvariant {T : Type} (ValueInst : Value T)
    (self : builder.Builder T) : Prop where
  layout : PackingLayout ValueInst self.packing_factor self.packing_depth
  level_valid : self.level.val = 0 ∨ self.packing_depth.val ≤ self.level.val
  builder_capacity_matches : self.capacity.val =
    subtreeCapacity self.packing_factor self.depth.val
  stack_dense : BuilderStack self.packing_factor self.stack.val self.depth.val
    self.length.val

theorem BuilderInvariant.length_le_capacity {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    (h : BuilderInvariant ValueInst self) :
    self.length.val ≤ self.capacity.val := by
  rw [BuilderInvariant.builder_capacity_matches h]
  exact (BuilderInvariant.stack_dense h).length_le_capacity

private theorem usize_shift_left_one_value {shift shifted : Std.Usize}
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

/-- Successful construction starts with the empty canonical stack. -/
theorem builder_new_establishes_invariant {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (depth level : Std.Usize)
    (hlevel : level.val = 0 ∨ packing_depth.val ≤ level.val)
    {self : builder.Builder T}
    (hnew : builder.Builder.new ValueInst depth level =
      ok (core.result.Result.Ok self)) :
    BuilderInvariant ValueInst self := by
  cases hlayout with
  | unpacked factor_eq depth_eq =>
    simp [builder.Builder.new, depth_eq, factor_eq, lift] at hnew
    cases hmax : MAX_TREE_DEPTH with
    | fail error => simp [hmax] at hnew
    | div => simp [hmax] at hnew
    | ok max_depth =>
      rw [hmax] at hnew
      simp only [bind_tc_ok] at hnew
      split at hnew
      · simp at hnew
      · cases hsum : depth + 0#usize with
        | fail error => simp [hsum] at hnew
        | div => simp [hsum] at hnew
        | ok sum =>
          rw [hsum] at hnew
          simp only [bind_tc_ok] at hnew
          cases hcapacity : 1#usize <<< sum with
          | fail error => simp [hcapacity] at hnew
          | div => simp [hcapacity] at hnew
          | ok capacity =>
            simp [hcapacity] at hnew
            subst self
            refine ⟨PackingLayout.unpacked factor_eq depth_eq, hlevel, ?_, ?_⟩
            · have hsum_val := UScalar.add_equiv depth 0#usize
              rw [hsum] at hsum_val
              have hcapacity_val := usize_shift_left_one_value hcapacity
              simp [subtreeCapacity, leafCapacity, hcapacity_val] at hsum_val ⊢
              omega
            · exact BuilderStack.empty depth.val
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    simp [builder.Builder.new, depth_eq, factor_eq, lift] at hnew
    cases hmax : MAX_TREE_DEPTH with
    | fail error => simp [hmax] at hnew
    | div => simp [hmax] at hnew
    | ok max_depth =>
      rw [hmax] at hnew
      simp only [bind_tc_ok] at hnew
      split at hnew
      · simp at hnew
      · cases hsum : depth + packing_depth with
        | fail error => simp [hsum] at hnew
        | div => simp [hsum] at hnew
        | ok sum =>
          rw [hsum] at hnew
          simp only [bind_tc_ok] at hnew
          cases hcapacity : 1#usize <<< sum with
          | fail error => simp [hcapacity] at hnew
          | div => simp [hcapacity] at hnew
          | ok capacity =>
            simp [hcapacity] at hnew
            subst self
            refine ⟨PackingLayout.packed factor packing_depth factor_eq
              depth_eq factor_is_power, hlevel, ?_, ?_⟩
            · change capacity.val = subtreeCapacity (some factor) depth.val
              have hsum_val := UScalar.add_equiv depth packing_depth
              rw [hsum] at hsum_val
              obtain ⟨-, hsum_value, -⟩ := hsum_val
              have hcapacity_val := usize_shift_left_one_value hcapacity
              rw [hcapacity_val, hsum_value]
              simp [subtreeCapacity, leafCapacity, factor_is_power, pow_add,
                Nat.mul_comm]
            · exact BuilderStack.empty depth.val

/-! ## Value insertion -/

/-- A successful append to a dense packed leaf increases its logical length
    by one. Success itself supplies the only required capacity condition. -/
theorem packedLeaf_push_preserves_dense {T : Type} (ValueInst : Value T)
    {factor packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst (some factor) packing_depth)
    {leaf updated : packed_leaf.PackedLeaf T} {len : Nat}
    (hdense : DenseTree (some factor) (Tree.PackedLeaf leaf) 0 len)
    (value : T)
    (hpush : packed_leaf.PackedLeaf.push
      ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst leaf value =
      ok (core.result.Result.Ok (), updated)) :
    DenseTree (some factor) (Tree.PackedLeaf updated) 0 (len + 1) := by
  cases hdense with
  | packed _ _ old_nonempty old_fit =>
    have hfactor := hlayout.tree_hash_packing_factor_eq
    unfold packed_leaf.PackedLeaf.push at hpush
    rw [hfactor] at hpush
    simp only [bind_tc_ok] at hpush
    by_cases hfull : leaf.values.len = factor
    · simp [hfull] at hpush
    · simp only [hfull, ↓reduceIte] at hpush
      cases hvalues : alloc.vec.Vec.push leaf.values value with
      | fail error => simp [hvalues] at hpush
      | div => simp [hvalues] at hpush
      | ok values =>
        simp [hvalues] at hpush
        subst updated
        have hlength : values.val.length = leaf.values.val.length + 1 := by
          unfold alloc.vec.Vec.push at hvalues
          simp at hvalues
          grind
        have hneq : leaf.values.val.length ≠ factor.val := by
          intro heq
          apply hfull
          apply UScalar.eq_of_val_eq
          simpa using heq
        have hnew := DenseTree.packed factor
          ({ hash := leaf.hash, values := values } : packed_leaf.PackedLeaf T)
          (by simp [hlength]) (by simp [hlength]; omega)
        simpa [hlength] using hnew

/-- A proof-relevant description of the full subtrees consumed by a builder
    carry. Each step removes the final stack entry, combines two equally deep
    full trees, and continues with the resulting full parent. -/
inductive BuilderMergePlan {T : Type} (ValueInst : Value T)
    (packing_factor : Option Std.Usize) :
    Nat → List (utils.MaybeArced (Tree T)) → Tree T →
      List (utils.MaybeArced (Tree T)) → Tree T → Nat → Prop where
  | done (stack : List (utils.MaybeArced (Tree T))) (top : Tree T)
      (depth : Nat)
      (top_dense : DenseTree packing_factor top depth
        (subtreeCapacity packing_factor depth)) :
      BuilderMergePlan ValueInst packing_factor 0 stack top stack top depth
  | step (base_stack : List (utils.MaybeArced (Tree T)))
      (left : utils.MaybeArced (Tree T)) (top merged : Tree T)
      (depth count : Nat)
      {final_stack : List (utils.MaybeArced (Tree T))}
      {final_top : Tree T} {final_depth : Nat}
      (left_dense : DenseTree packing_factor (maybeArcedTree left) depth
        (subtreeCapacity packing_factor depth))
      (top_dense : DenseTree packing_factor top depth
        (subtreeCapacity packing_factor depth))
      (merge_eq : Tree.node_unboxed ValueInst (maybeArcedTree left) top =
        ok merged)
      (remaining : BuilderMergePlan ValueInst packing_factor count base_stack
        merged final_stack final_top final_depth) :
      BuilderMergePlan ValueInst packing_factor (count + 1)
        (base_stack ++ [left]) top final_stack final_top final_depth

theorem BuilderMergePlan.final_dense {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {count : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth : Nat}
    (h : BuilderMergePlan ValueInst packing_factor count stack top final_stack
      final_top final_depth) :
    DenseTree packing_factor final_top final_depth
      (subtreeCapacity packing_factor final_depth) := by
  induction h with
  | done stack top depth top_dense => exact top_dense
  | step base_stack left top merged depth count left_dense top_dense merge_eq
      remaining ih =>
    exact ih

private theorem vec_pop_append_last {A X : Type}
    (source : alloc.vec.Vec X) (items : List X) (last : X)
    (hsource : source.val = items ++ [last]) :
    ∃ rest : alloc.vec.Vec X,
      alloc.vec.Vec.pop A source = ok (some last, rest) ∧
        rest.val = items := by
  have bound : (items ++ [last]).length ≤ Usize.max := by
    simpa [hsource] using source.property
  let explicit : alloc.vec.Vec X := ⟨items ++ [last], bound⟩
  have hexplicit : source = explicit := by
    apply Subtype.ext
    simpa [explicit] using hsource
  subst source
  let rest : alloc.vec.Vec X := ⟨items, by
    have hle : items.length ≤ (items ++ [last]).length := by simp
    exact hle.trans bound⟩
  refine ⟨rest, ?_, rfl⟩
  have hreverse : (items ++ [last]).reverse = last :: items.reverse := by simp
  unfold alloc.vec.Vec.pop
  split
  · rename_i hempty
    rw [hreverse] at hempty
    simp at hempty
  · rename_i head tail hcons
    rw [hreverse] at hcons
    cases hcons
    simp [rest]

private theorem vec_push_values {X : Type} (items : alloc.vec.Vec X) (last : X)
    {result : alloc.vec.Vec X}
    (h : alloc.vec.Vec.push items last = ok result) :
    result.val = items.val ++ [last] := by
  unfold alloc.vec.Vec.push at h
  simp at h
  grind

private theorem push_loop0_step {T : Type} (ValueInst : Value T)
    (iter : core.ops.range.Range Std.U32)
    (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
    (length : utils.Length) (top : Tree T) :
    builder.Builder.push_loop0 ValueInst iter stack length top =
      match builder.Builder.push_loop0.body ValueInst length iter stack top with
      | ok (.cont (iter1, stack1, top1)) =>
        builder.Builder.push_loop0 ValueInst iter1 stack1 length top1
      | ok (.done result) => ok result
      | fail error => fail error
      | div => div := by
  conv_lhs => unfold builder.Builder.push_loop0
  conv_lhs => unfold Aeneas.Std.loop
  cases hbody : builder.Builder.push_loop0.body ValueInst length iter stack top with
  | fail error => simp [hbody]
  | div => simp [hbody]
  | ok flow =>
    cases flow with
    | cont state =>
      obtain ⟨iter1, stack1, top1⟩ := state
      simp [hbody]
      rfl
    | done result => simp [hbody]

private theorem range_u32_next_none
    (iter : core.ops.range.Range Std.U32)
    (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
      ok (none, iter) := by
  have hspec :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
        ⦃ option iter1 => option = none ∧ iter1 = iter ⦄ :=
    core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty := .U32) (by intros; rfl) iter hge
  cases hnext : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter with
  | fail error => rw [hnext] at hspec; simp at hspec
  | div => rw [hnext] at hspec; simp at hspec
  | ok result =>
    rw [hnext] at hspec
    simp at hspec
    obtain ⟨option, iter1⟩ := result
    change option = none ∧ iter1 = iter at hspec
    obtain ⟨rfl, rfl⟩ := hspec
    rfl

private theorem range_u32_next_some
    (iter : core.ops.range.Range Std.U32)
    (hlt : iter.start.val < iter.end.val) :
    ∃ iter1,
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
        ok (some iter.start, iter1) ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end := by
  have hspec :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
        ⦃ option iter1 => option = some iter.start ∧
          iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ⦄ :=
    core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty := .U32) (by intros; rfl) (by intros; rfl) iter hlt
  cases hnext : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter with
  | fail error => rw [hnext] at hspec; simp at hspec
  | div => rw [hnext] at hspec; simp at hspec
  | ok result =>
    rw [hnext] at hspec
    simp at hspec
    obtain ⟨option, iter1⟩ := result
    change option = some iter.start ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end at hspec
    obtain ⟨rfl, hstart, hend⟩ := hspec
    exact ⟨iter1, by simp, hstart, hend⟩

private theorem usize_add_one_value {value next : Std.Usize}
    (h : value + 1#usize = ok next) : next.val = value.val + 1 := by
  have hadd := UScalar.add_equiv value 1#usize
  rw [h] at hadd
  simp at hadd
  omega

private theorem push_loop0_follows_merge_plan {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {count : Nat} {input_stack : List (utils.MaybeArced (Tree T))}
    {input_top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth : Nat}
    (hplan : BuilderMergePlan ValueInst packing_factor count input_stack
      input_top final_stack final_top final_depth) :
    ∀ (iter : core.ops.range.Range Std.U32)
      (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
      (length : utils.Length)
      (result_stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
      (result_length : utils.Length),
      iter.end.val = iter.start.val + count →
      stack.val = input_stack →
      builder.Builder.push_loop0 ValueInst iter stack length input_top =
        ok (core.result.Result.Ok (), result_stack, result_length) →
      result_stack.val = final_stack ++
          [utils.MaybeArced.Unarced final_top] ∧
        result_length.val = length.val + 1 := by
  induction hplan with
  | done plan_stack top depth top_dense =>
    intro iter stack length result_stack result_length hremaining hstack hloop
    have hge : iter.start.val ≥ iter.end.val := by omega
    have hnext := range_u32_next_none iter hge
    rw [push_loop0_step] at hloop
    unfold builder.Builder.push_loop0.body at hloop
    simp only [hnext, bind_tc_ok] at hloop
    cases hpush : alloc.vec.Vec.push stack (utils.MaybeArced.Unarced top) with
    | fail error => simp [hpush] at hloop
    | div => simp [hpush] at hloop
    | ok pushed =>
      rw [hpush] at hloop
      simp only [bind_tc_ok] at hloop
      cases hadd : length + 1#usize with
      | fail error => simp [utils.Length.as_mut, hadd] at hloop
      | div => simp [utils.Length.as_mut, hadd] at hloop
      | ok next_length =>
        simp [utils.Length.as_mut, hadd] at hloop
        obtain ⟨rfl, rfl⟩ := hloop
        have hpushed := vec_push_values stack
          (utils.MaybeArced.Unarced top) hpush
        exact ⟨by simpa [hstack] using hpushed, usize_add_one_value hadd⟩
  | @step base_stack left top merged depth remaining_count final_stack
      final_top final_depth left_dense top_dense merge_eq remaining ih =>
    intro iter stack length result_stack result_length hremaining hstack hloop
    have hlt : iter.start.val < iter.end.val := by omega
    obtain ⟨iter1, hnext, hstart, hend⟩ := range_u32_next_some iter hlt
    have hbound : (base_stack ++ [left]).length ≤ Usize.max := by
      simpa [hstack] using stack.property
    let source : alloc.vec.Vec (utils.MaybeArced (Tree T)) :=
      ⟨base_stack ++ [left], hbound⟩
    have hsource : stack = source := by
      apply Subtype.ext
      simpa [source] using hstack
    subst stack
    obtain ⟨rest, hpop, hrest⟩ :=
      vec_pop_append_last (A := Global) source base_stack left rfl
    rw [push_loop0_step] at hloop
    unfold builder.Builder.push_loop0.body at hloop
    simp [hnext, hpop, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      maybeArced_arced, merge_eq] at hloop
    apply ih iter1 rest length result_stack result_length
    · have hend_value := congrArg UScalar.val hend
      omega
    · exact hrest
    · exact hloop

private theorem push_loop1_eq_loop0 {T : Type} (ValueInst : Value T)
    (iter : core.ops.range.Range Std.U32)
    (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
    (length : utils.Length) (top : Tree T) :
    builder.Builder.push_loop1 ValueInst iter stack length top =
      builder.Builder.push_loop0 ValueInst iter stack length top := by
  rfl

private theorem push_loop2_eq_loop0 {T : Type} (ValueInst : Value T)
    (iter : core.ops.range.Range Std.U32)
    (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
    (length : utils.Length) (top : Tree T) :
    builder.Builder.push_loop2 ValueInst iter stack length top =
      builder.Builder.push_loop0 ValueInst iter stack length top := by
  rfl

end milhouse.tree
