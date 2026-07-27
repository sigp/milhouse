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

end milhouse.tree
