-- Builder stack invariants and preservation.
import Tree.Invariants
import Mathlib.NumberTheory.Padics.PadicVal.Basic

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
inductive BuilderStack {T : Type} (packing_factor : Option Std.Usize)
    (base_depth : Nat) :
    List (utils.MaybeArced (Tree T)) → Nat → Nat → Prop where
  | empty (depth : Nat) (base_le_depth : base_depth ≤ depth) :
      BuilderStack packing_factor base_depth [] depth 0
  | base (entry : utils.MaybeArced (Tree T)) (len : Nat)
      (dense : DenseTree packing_factor (maybeArcedTree entry) base_depth len)
      (nonempty : 0 < len) :
      BuilderStack packing_factor base_depth [entry] base_depth len
  | full (entry : utils.MaybeArced (Tree T)) (depth : Nat)
      (base_le_depth : base_depth ≤ depth)
      (dense : DenseTree packing_factor (maybeArcedTree entry) depth
        (subtreeCapacity packing_factor depth))
      (capacity_nonempty : 0 < subtreeCapacity packing_factor depth) :
      BuilderStack packing_factor base_depth [entry] depth
        (subtreeCapacity packing_factor depth)
  | segment (entry : utils.MaybeArced (Tree T)) (depth len : Nat)
      (base_le_depth : base_depth ≤ depth)
      (dense : DenseTree packing_factor (maybeArcedTree entry) depth len)
      (nonempty : 0 < len)
      (full_or_unaligned :
        len = subtreeCapacity packing_factor depth ∨
          len % subtreeCapacity packing_factor base_depth ≠ 0) :
      BuilderStack packing_factor base_depth [entry] depth len
  | left {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
      (child_prefix : BuilderStack packing_factor base_depth stack depth len)
      (fits_left : len ≤ subtreeCapacity packing_factor depth) :
      BuilderStack packing_factor base_depth stack (depth + 1) len
  | right (left : utils.MaybeArced (Tree T))
      {right_stack : List (utils.MaybeArced (Tree T))}
      (depth right_len : Nat)
      (left_dense : DenseTree packing_factor (maybeArcedTree left) depth
        (subtreeCapacity packing_factor depth))
      (right_prefix : BuilderStack packing_factor base_depth right_stack depth
        right_len)
      (right_nonempty : 0 < right_len)
      (right_not_full : right_len < subtreeCapacity packing_factor depth) :
      BuilderStack packing_factor base_depth (left :: right_stack) (depth + 1)
        (subtreeCapacity packing_factor depth + right_len)

theorem BuilderStack.length_le_capacity {T : Type}
    {packing_factor : Option Std.Usize}
    {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len) :
    len ≤ subtreeCapacity packing_factor depth := by
  induction h with
  | empty => simp
  | base entry len dense nonempty => exact dense.length_le_capacity
  | full => exact Nat.le_refl _
  | segment entry depth len base_le_depth dense nonempty full_or_unaligned =>
    exact dense.length_le_capacity
  | @left stack child_depth child_len child_prefix fits_left ih =>
    have hcap : subtreeCapacity packing_factor (child_depth + 1) =
        2 * subtreeCapacity packing_factor child_depth := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
    rw [hcap]
    omega
  | @right left right_stack child_depth right_len left_dense right_prefix
      right_nonempty right_not_full ih =>
    have hcap : subtreeCapacity packing_factor (child_depth + 1) =
        2 * subtreeCapacity packing_factor child_depth := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
    rw [hcap]
    have hright := ih
    omega

theorem BuilderStack.base_le_depth {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len) :
    base_depth ≤ depth := by
  induction h with
  | empty depth base_le_depth => exact base_le_depth
  | base => exact Nat.le_refl _
  | full entry depth base_le_depth dense capacity_nonempty => exact base_le_depth
  | segment entry depth len base_le_depth dense nonempty full_or_unaligned =>
    exact base_le_depth
  | left child_prefix fits_left ih => omega
  | right left depth right_len left_dense right_prefix right_nonempty
      right_not_full ih => omega

private theorem subtreeCapacity_succ (packing_factor : Option Std.Usize)
    (depth : Nat) :
    subtreeCapacity packing_factor (depth + 1) =
      2 * subtreeCapacity packing_factor depth := by
  simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]

private theorem subtreeCapacity_eq_mul_pow_of_le
    (packing_factor : Option Std.Usize) {base depth : Nat}
    (hle : base ≤ depth) :
    subtreeCapacity packing_factor depth =
      subtreeCapacity packing_factor base * 2 ^ (depth - base) := by
  have hdepth : depth = base + (depth - base) := by omega
  rw [hdepth]
  simp [subtreeCapacity, pow_add, Nat.mul_assoc]

private theorem subtreeCapacity_strictMono {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {lower upper : Nat} (hlt : lower < upper) :
    subtreeCapacity packing_factor lower <
      subtreeCapacity packing_factor upper := by
  rw [subtreeCapacity_eq_mul_pow_of_le packing_factor (Nat.le_of_lt hlt)]
  apply lt_mul_of_one_lt_right (hlayout.subtreeCapacity_pos lower)
  exact Nat.one_lt_two_pow (by omega)

private theorem aligned_add_le {unit total limit added : Nat}
    (hunit : 0 < unit) (htotal : total % unit = 0)
    (hlimit : limit % unit = 0) (hlt : total < limit)
    (hadded : added ≤ unit) :
    total + added ≤ limit := by
  have htotal_dvd : unit ∣ total := Nat.dvd_of_mod_eq_zero htotal
  have hlimit_dvd : unit ∣ limit := Nat.dvd_of_mod_eq_zero hlimit
  obtain ⟨total_units, rfl⟩ := htotal_dvd
  obtain ⟨limit_units, rfl⟩ := hlimit_dvd
  have hunits : total_units < limit_units := by
    exact (Nat.mul_lt_mul_left hunit).mp (by simpa [Nat.mul_comm] using hlt)
  calc
    unit * total_units + added ≤ unit * total_units + unit :=
      Nat.add_le_add_left hadded _
    _ = unit * (total_units + 1) := by simp [Nat.mul_add]
    _ ≤ unit * limit_units :=
      Nat.mul_le_mul_left unit (Nat.succ_le_iff.mpr hunits)

private theorem natTrailingZeros_eq_padicValNat :
    ∀ fuel n : Nat, 0 < n → padicValNat 2 n ≤ fuel →
      TreeAux.natTrailingZeros fuel n = padicValNat 2 n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hbound
    have hzero : padicValNat 2 n = 0 := by omega
    simp [TreeAux.natTrailingZeros, hzero]
  | succ fuel ih =>
    intro n hn hbound
    unfold TreeAux.natTrailingZeros
    by_cases heven : n % 2 = 0
    · rw [if_pos heven]
      have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
      have hn_two : 2 ≤ n := Nat.le_of_dvd hn hdvd
      have hdiv_pos : 0 < n / 2 := Nat.div_pos hn_two (by omega)
      have hval_ne : padicValNat 2 n ≠ 0 :=
        (dvd_iff_padicValNat_ne_zero (p := 2) hn.ne').mp hdvd
      have hdiv_val := padicValNat.div (p := 2) hdvd
      rw [ih (n / 2) hdiv_pos (by omega), hdiv_val]
      omega
    · rw [if_neg heven]
      have hnot_dvd : ¬2 ∣ n := by
        intro hdvd
        exact heven (Nat.mod_eq_zero_of_dvd hdvd)
      rw [padicValNat.eq_zero_of_not_dvd hnot_dvd]

private theorem natTrailingZeros_le_fuel :
    ∀ fuel n : Nat, TreeAux.natTrailingZeros fuel n ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro n; simp [TreeAux.natTrailingZeros]
  | succ fuel ih =>
    intro n
    unfold TreeAux.natTrailingZeros
    split
    · have := ih (n / 2)
      omega
    · omega

private theorem usize_trailing_zeros_padic {value : Std.Usize} {zeros : Std.U32}
    (hvalue : 0 < value.val)
    (hzeros : core.num.Usize.trailing_zeros value = ok zeros) :
    zeros.val = padicValNat 2 value.val := by
  have hbv : value.bv ≠ 0 := by
    intro hzero
    have hval_zero : value.val = 0 := by
      change value.bv.toNat = 0
      rw [hzero]
      rfl
    omega
  have htz_le := natTrailingZeros_le_fuel System.Platform.numBits value.val
  have hpadic_le : padicValNat 2 value.val ≤ System.Platform.numBits := by
    have hpow_le : 2 ^ padicValNat 2 value.val ≤ value.val :=
      Nat.le_of_dvd hvalue pow_padicValNat_dvd
    by_contra hnot_le
    have hpow_lt : 2 ^ System.Platform.numBits <
        2 ^ padicValNat 2 value.val :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hbits : value.val < 2 ^ System.Platform.numBits := by
      simpa using value.hBounds
    omega
  unfold core.num.Usize.trailing_zeros at hzeros
  have hzero_eq : zeros =
      ⟨BitVec.ofNat 32 (TreeAux.bvTrailingZeros value.bv)⟩ := by
    injection hzeros with heq
    exact heq.symm
  subst zeros
  change (BitVec.ofNat 32 (TreeAux.bvTrailingZeros value.bv)).toNat =
    padicValNat 2 value.val
  unfold TreeAux.bvTrailingZeros
  rw [if_neg hbv]
  change (BitVec.ofNat 32
    (TreeAux.natTrailingZeros System.Platform.numBits value.val)).toNat =
      padicValNat 2 value.val
  rw [natTrailingZeros_eq_padicValNat System.Platform.numBits value.val
    hvalue hpadic_le]
  simp only [BitVec.toNat_ofNat]
  have hword : System.Platform.numBits < 2 ^ 32 := by native_decide
  have : padicValNat 2 value.val < 2 ^ 32 := by omega
  exact Nat.mod_eq_of_lt this

private theorem padicValNat_two_pow_add_of_lt {exponent value : Nat}
    (hvalue : 0 < value)
    (hvaluation : padicValNat 2 value < exponent) :
    padicValNat 2 (2 ^ exponent + value) = padicValNat 2 value := by
  let valuation := padicValNat 2 value
  have hsum : 0 < 2 ^ exponent + value := by positivity
  apply Nat.le_antisymm
  · by_contra hnot_le
    have hsucc : valuation + 1 ≤ padicValNat 2 (2 ^ exponent + value) := by
      omega
    have hsum_dvd : 2 ^ (valuation + 1) ∣ 2 ^ exponent + value :=
      (padicValNat_dvd_iff_le (p := 2) hsum.ne').mpr hsucc
    have hpow_dvd : 2 ^ (valuation + 1) ∣ 2 ^ exponent :=
      pow_dvd_pow 2 (by omega)
    have hvalue_dvd : 2 ^ (valuation + 1) ∣ value := by
      have := Nat.dvd_sub hsum_dvd hpow_dvd
      simpa using this
    exact pow_succ_padicValNat_not_dvd (p := 2) hvalue.ne' hvalue_dvd
  · have hvalue_dvd : 2 ^ valuation ∣ value := pow_padicValNat_dvd
    have hpow_dvd : 2 ^ valuation ∣ 2 ^ exponent :=
      pow_dvd_pow 2 (Nat.le_of_lt hvaluation)
    have hsum_dvd : 2 ^ valuation ∣ 2 ^ exponent + value :=
      Nat.dvd_add hpow_dvd hvalue_dvd
    exact (padicValNat_dvd_iff_le (p := 2) hsum.ne').mp hsum_dvd

/-- A canonical stack at full capacity has already performed every carry, so
    it consists of exactly one full tree at the root depth. -/
theorem BuilderStack.full_single {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len)
    (hfull : len = subtreeCapacity packing_factor depth) :
    ∃ entry, stack = [entry] ∧
      DenseTree packing_factor (maybeArcedTree entry) depth
        (subtreeCapacity packing_factor depth) := by
  induction h with
  | empty depth base_le_depth =>
    have hpos := hlayout.subtreeCapacity_pos depth
    omega
  | base entry len dense nonempty =>
    exact ⟨entry, rfl, by simpa [hfull] using dense⟩
  | full entry depth base_le_depth dense capacity_nonempty =>
    exact ⟨entry, rfl, dense⟩
  | segment entry depth len base_le_depth dense nonempty full_or_unaligned =>
    exact ⟨entry, rfl, by simpa [hfull] using dense⟩
  | @left stack child_depth child_len child_prefix fits_left ih =>
    rw [subtreeCapacity_succ] at hfull
    have hpos := hlayout.subtreeCapacity_pos child_depth
    omega
  | @right left right_stack child_depth right_len left_dense right_prefix
      right_nonempty right_not_full ih =>
    rw [subtreeCapacity_succ] at hfull
    omega

theorem BuilderStack.eq_nil_of_length_zero {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len)
    (hzero : len = 0) : stack = [] := by
  induction h with
  | empty => rfl
  | base entry len dense nonempty => omega
  | full entry depth base_le_depth dense capacity_nonempty => omega
  | segment entry depth len base_le_depth dense nonempty full_or_unaligned =>
    omega
  | left child_prefix fits_left ih => exact ih hzero
  | right left depth right_len left_dense right_prefix
      right_nonempty right_not_full ih => omega

theorem BuilderStack.ne_nil_of_length_pos {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len)
    (hpos : 0 < len) : stack ≠ [] := by
  induction h with
  | empty => omega
  | base => simp
  | full => simp
  | segment => simp
  | left child_prefix fits_left ih => exact ih hpos
  | right => simp

theorem BuilderStack.raise_left {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len)
    (extra : Nat) :
    BuilderStack packing_factor base_depth stack (depth + extra) len := by
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
    rw [Nat.add_succ]
    exact BuilderStack.left ih ih.length_le_capacity

/-- `Arced` and `Unarced` are ownership details erased by the translation;
    replacing stack entries without changing their trees preserves shape. -/
theorem BuilderStack.rewrap {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack replacement : List (utils.MaybeArced (Tree T))}
    {depth len : Nat}
    (hstack : BuilderStack packing_factor base_depth stack depth len)
    (hsame : stack.map maybeArcedTree = replacement.map maybeArcedTree) :
    BuilderStack packing_factor base_depth replacement depth len := by
  induction hstack generalizing replacement with
  | empty depth base_le_depth =>
    have hreplacement : replacement = [] := by
      simpa using hsame.symm
    subst replacement
    exact BuilderStack.empty depth base_le_depth
  | base entry len dense nonempty =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement tail =>
      have hparts : maybeArcedTree entry = maybeArcedTree replacement ∧
          tail = [] := by
        simpa using hsame
      obtain ⟨htree, rfl⟩ := hparts
      exact BuilderStack.base replacement len (by simpa [← htree] using dense)
        nonempty
  | full entry depth base_le_depth dense capacity_nonempty =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement tail =>
      have hparts : maybeArcedTree entry = maybeArcedTree replacement ∧
          tail = [] := by
        simpa using hsame
      obtain ⟨htree, rfl⟩ := hparts
      exact BuilderStack.full replacement depth base_le_depth
        (by simpa [← htree] using dense) capacity_nonempty
  | segment entry depth len base_le_depth dense nonempty full_or_unaligned =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement tail =>
      have hparts : maybeArcedTree entry = maybeArcedTree replacement ∧
          tail = [] := by
        simpa using hsame
      obtain ⟨htree, rfl⟩ := hparts
      exact BuilderStack.segment replacement depth len base_le_depth
        (by simpa [← htree] using dense) nonempty full_or_unaligned
  | left child_prefix fits_left ih =>
    exact BuilderStack.left (ih hsame) fits_left
  | @right left right_stack depth right_len left_dense right_prefix right_nonempty
      right_not_full ih =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement replacement_tail =>
      have hparts : maybeArcedTree left = maybeArcedTree replacement ∧
          right_stack.map maybeArcedTree =
            replacement_tail.map maybeArcedTree := by
        simpa using hsame
      obtain ⟨hleft, htail⟩ := hparts
      exact BuilderStack.right replacement depth right_len
        (by simpa [← hleft] using left_dense) (ih htail) right_nonempty
        right_not_full

/-- The translated builder fields agree with its packing layout and its stack
    is the canonical decomposition of the reported dense prefix. The level
    restriction records the two modes created inside this crate: leaf level
    zero, or a level at/above the packing boundary. -/
structure BuilderInvariant {T : Type} (ValueInst : Value T)
    (self : builder.Builder T) : Prop where
  layout : PackingLayout ValueInst self.packing_factor self.packing_depth
  level_valid : self.level.val = 0 ∨ self.packing_depth.val ≤ self.level.val
  level_bounded : self.level.val ≤ self.depth.val + self.packing_depth.val
  builder_capacity_matches : self.capacity.val =
    subtreeCapacity self.packing_factor self.depth.val
  stack_dense : BuilderStack self.packing_factor
    (if self.level.val = 0 then 0 else self.level.val - self.packing_depth.val)
    self.stack.val self.depth.val self.length.val

theorem BuilderInvariant.length_le_capacity {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    (h : BuilderInvariant ValueInst self) :
    self.length.val ≤ self.capacity.val := by
  rw [BuilderInvariant.builder_capacity_matches h]
  exact (BuilderInvariant.stack_dense h).length_le_capacity

/-- At every level where `push_node` is used, one stack entry represents
    exactly `2^level` logical values. Packed level zero is excluded because
    that mode appends individual values through `push` instead. -/
theorem BuilderInvariant.base_capacity_eq_pow_level {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    (h : BuilderInvariant ValueInst self)
    (hnode_level : self.level.val ≠ 0 ∨ self.packing_factor = none) :
    subtreeCapacity self.packing_factor
        (if self.level.val = 0 then 0
          else self.level.val - self.packing_depth.val) =
      2 ^ self.level.val := by
  by_cases hlevel : self.level.val = 0
  · have hfactor : self.packing_factor = none := hnode_level.resolve_left
      (not_not.mpr hlevel)
    simp [hlevel, hfactor, subtreeCapacity, leafCapacity]
  · rw [if_neg hlevel,
      (BuilderInvariant.layout h).subtreeCapacity_eq_two_pow]
    have hpacking_le : self.packing_depth.val ≤ self.level.val :=
      (BuilderInvariant.level_valid h).resolve_left hlevel
    congr 1
    omega

private theorem usize_checked_add_value {left right sum : Std.Usize}
    (h : Usize.checked_add left right = some sum) :
    sum.val = left.val + right.val := by
  have hspec := Usize.checked_add_bv_spec left right
  rw [h] at hspec
  exact hspec.2.1

private theorem usize_shift_right_value {value shift shifted : Std.Usize}
    (h : value >>> shift = ok shifted) :
    shifted.val = value.val >>> shift.val := by
  have hbound : shift.val < System.Platform.numBits := by
    change UScalar.shiftRight value shift.val = ok shifted at h
    unfold UScalar.shiftRight at h
    split at h
    · assumption
    · simp at h
  have hspec := Std.Usize.ShiftRight_spec value shift hbound
  rw [h] at hspec
  exact hspec.1

private theorem u32_saturating_sub_value (left right : Std.U32) :
    (core.num.U32.saturating_sub left right).val = left.val - right.val := by
  change (BitVec.ofNat 32 (max 0 (left.val - right.val))).toNat =
    left.val - right.val
  rw [max_eq_right (Nat.zero_le _), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt]
  exact (Nat.sub_le left.val right.val).trans_lt left.hBounds

private theorem PackingLayout.packing_depth_lt_u32 {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth) :
    packing_depth.val < 2 ^ 32 := by
  cases hlayout with
  | unpacked => simp
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    have hdepth_bits : packing_depth.val < System.Platform.numBits := by
      by_contra hnot_lt
      have hpow_le : 2 ^ System.Platform.numBits ≤
          2 ^ packing_depth.val :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [← factor_is_power] at hpow_le
      exact (Nat.not_le_of_gt factor.hBounds) hpow_le
    have hbits : System.Platform.numBits < 2 ^ 32 := by native_decide
    omega

private theorem PackingLayout.packing_depth_cast_u32 {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth) :
    (UScalar.cast .U32 packing_depth).val = packing_depth.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hlayout.packing_depth_lt_u32

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
    (hlevel_bound : level.val ≤ depth.val + packing_depth.val)
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
            refine ⟨PackingLayout.unpacked factor_eq depth_eq, hlevel,
              hlevel_bound, ?_, ?_⟩
            · have hsum_val := UScalar.add_equiv depth 0#usize
              rw [hsum] at hsum_val
              have hcapacity_val := usize_shift_left_one_value hcapacity
              simp [subtreeCapacity, leafCapacity, hcapacity_val] at hsum_val ⊢
              omega
            · change BuilderStack none
                (if level.val = 0 then 0 else level.val - (0#usize).val)
                [] depth.val 0
              apply BuilderStack.empty depth.val
              split <;> omega
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
              depth_eq factor_is_power, hlevel, hlevel_bound, ?_, ?_⟩
            · change capacity.val = subtreeCapacity (some factor) depth.val
              have hsum_val := UScalar.add_equiv depth packing_depth
              rw [hsum] at hsum_val
              obtain ⟨-, hsum_value, -⟩ := hsum_val
              have hcapacity_val := usize_shift_left_one_value hcapacity
              rw [hcapacity_val, hsum_value]
              simp [subtreeCapacity, leafCapacity, factor_is_power, pow_add,
                Nat.mul_comm]
            · change BuilderStack (some factor)
                (if level.val = 0 then 0 else
                  level.val - packing_depth.val) [] depth.val 0
              apply BuilderStack.empty depth.val
              split <;> omega

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

/-- A proof-relevant description of the subtrees consumed by a builder carry.
    Each step removes a full final stack entry and combines it with the
    nonempty dense prefix to its right. The right prefix may be partial, which
    is required by `push_node`. -/
inductive BuilderMergePlan {T : Type} (ValueInst : Value T)
    (packing_factor : Option Std.Usize) :
    Nat → List (utils.MaybeArced (Tree T)) → Tree T →
      List (utils.MaybeArced (Tree T)) → Tree T → Nat → Nat → Prop where
  | done (stack : List (utils.MaybeArced (Tree T))) (top : Tree T)
      (depth len : Nat)
      (top_dense : DenseTree packing_factor top depth len)
      (top_nonempty : 0 < len) :
      BuilderMergePlan ValueInst packing_factor 0 stack top stack top depth len
  | step (base_stack : List (utils.MaybeArced (Tree T)))
      (left : utils.MaybeArced (Tree T)) (top merged : Tree T)
      (depth top_len count : Nat)
      {final_stack : List (utils.MaybeArced (Tree T))}
      {final_top : Tree T} {final_depth final_len : Nat}
      (left_dense : DenseTree packing_factor (maybeArcedTree left) depth
        (subtreeCapacity packing_factor depth))
      (top_dense : DenseTree packing_factor top depth top_len)
      (top_nonempty : 0 < top_len)
      (merge_eq : Tree.node_unboxed ValueInst (maybeArcedTree left) top =
        ok merged)
      (remaining : BuilderMergePlan ValueInst packing_factor count base_stack
        merged final_stack final_top final_depth final_len) :
      BuilderMergePlan ValueInst packing_factor (count + 1)
        (base_stack ++ [left]) top final_stack final_top final_depth final_len

theorem BuilderMergePlan.final_dense {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {count : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth final_len : Nat}
    (h : BuilderMergePlan ValueInst packing_factor count stack top final_stack
      final_top final_depth final_len) :
    DenseTree packing_factor final_top final_depth final_len := by
  induction h with
  | done stack top depth len top_dense top_nonempty => exact top_dense
  | step base_stack left top merged depth top_len count left_dense top_dense
      top_nonempty merge_eq remaining ih =>
    exact ih

theorem BuilderMergePlan.prepend {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {count : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth final_len : Nat}
    (leading : List (utils.MaybeArced (Tree T)))
    (h : BuilderMergePlan ValueInst packing_factor count stack top final_stack
      final_top final_depth final_len) :
    BuilderMergePlan ValueInst packing_factor count (leading ++ stack) top
      (leading ++ final_stack) final_top final_depth final_len := by
  induction h generalizing leading with
  | done stack top depth len top_dense top_nonempty =>
    exact BuilderMergePlan.done (leading ++ stack) top depth len top_dense
      top_nonempty
  | step base_stack left top merged depth top_len count left_dense top_dense
      top_nonempty merge_eq remaining ih =>
    have hremaining := ih leading
    have hstep := BuilderMergePlan.step (leading ++ base_stack) left top merged
      depth top_len count left_dense top_dense top_nonempty merge_eq hremaining
    simpa [List.append_assoc] using hstep

theorem BuilderMergePlan.trans {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {first_count second_count : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {top : Tree T}
    {middle_stack : List (utils.MaybeArced (Tree T))}
    {middle_top : Tree T} {middle_depth middle_len : Nat}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth final_len : Nat}
    (first : BuilderMergePlan ValueInst packing_factor first_count stack top
      middle_stack middle_top middle_depth middle_len)
    (second : BuilderMergePlan ValueInst packing_factor second_count
      middle_stack middle_top final_stack final_top final_depth final_len) :
    BuilderMergePlan ValueInst packing_factor (first_count + second_count)
      stack top final_stack final_top final_depth final_len := by
  induction first with
  | done stack top depth len top_dense top_nonempty => simpa using second
  | step base_stack left top merged depth top_len count left_dense top_dense
      top_nonempty merge_eq remaining ih =>
    have hstep := BuilderMergePlan.step base_stack left top merged depth top_len
      (count + second_count) left_dense top_dense top_nonempty merge_eq
      (ih second)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

/-- Number of binary carries performed when one base subtree is appended at
    an aligned cursor. This numeric relation mirrors the recursive stack
    decomposition and is later connected to Rust's `trailing_zeros` count. -/
inductive BuilderCarryCount (packing_factor : Option Std.Usize)
    (base_depth : Nat) : Nat → Nat → Nat → Prop where
  | zero (root_depth : Nat) (base_le_root : base_depth ≤ root_depth) :
      BuilderCarryCount packing_factor base_depth root_depth 0 0
  | inside (child_depth total count : Nat)
      (child_count : BuilderCarryCount packing_factor base_depth child_depth
        total count)
      (not_at_right : total < subtreeCapacity packing_factor child_depth) :
      BuilderCarryCount packing_factor base_depth (child_depth + 1) total count
  | enter_right (child_depth : Nat) (base_lt_child : base_depth < child_depth) :
      BuilderCarryCount packing_factor base_depth (child_depth + 1)
        (subtreeCapacity packing_factor child_depth) 0
  | first_merge :
      BuilderCarryCount packing_factor base_depth (base_depth + 1)
        (subtreeCapacity packing_factor base_depth) 1
  | right_open (child_depth right_len count : Nat)
      (right_count : BuilderCarryCount packing_factor base_depth child_depth
        right_len count)
      (cursor_open : right_len + subtreeCapacity packing_factor base_depth <
        subtreeCapacity packing_factor child_depth) :
      BuilderCarryCount packing_factor base_depth (child_depth + 1)
        (subtreeCapacity packing_factor child_depth + right_len) count
  | right_close (child_depth right_len count : Nat)
      (right_count : BuilderCarryCount packing_factor base_depth child_depth
        right_len count)
      (cursor_closes : right_len + subtreeCapacity packing_factor base_depth =
        subtreeCapacity packing_factor child_depth) :
      BuilderCarryCount packing_factor base_depth (child_depth + 1)
        (subtreeCapacity packing_factor child_depth + right_len) (count + 1)

theorem BuilderCarryCount.base_le_depth
    {packing_factor : Option Std.Usize} {base_depth root_depth total count : Nat}
    (hcarry : BuilderCarryCount packing_factor base_depth root_depth total
      count) : base_depth ≤ root_depth := by
  induction hcarry with
  | zero root_depth base_le_root => exact base_le_root
  | inside child_depth total count child_count not_at_right ih => omega
  | enter_right child_depth base_lt_child => omega
  | first_merge => omega
  | right_open child_depth right_len count right_count cursor_open ih => omega
  | right_close child_depth right_len count right_count cursor_closes ih => omega

/-- The structural carry count is the two-adic valuation of the next base
    subtree index. Keeping the quotient as an existential avoids adding a
    division premise: alignment is already encoded by `BuilderCarryCount`. -/
theorem BuilderCarryCount.eq_padic_units {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth root_depth total count : Nat}
    (hcarry : BuilderCarryCount packing_factor base_depth root_depth total
      count) :
    ∃ units, total = subtreeCapacity packing_factor base_depth * units ∧
      count = padicValNat 2 (units + 1) := by
  have hbase_pos := hlayout.subtreeCapacity_pos base_depth
  induction hcarry with
  | zero root_depth base_le_root =>
    exact ⟨0, by simp, by simp⟩
  | inside child_depth total count child_count not_at_right ih =>
    exact ih
  | enter_right child_depth base_lt_child =>
    let exponent := child_depth - base_depth
    have hexponent_pos : 0 < exponent := by simp [exponent]; omega
    refine ⟨2 ^ exponent, ?_, ?_⟩
    · exact subtreeCapacity_eq_mul_pow_of_le packing_factor
        (Nat.le_of_lt base_lt_child)
    · have hnot_dvd : ¬2 ∣ 2 ^ exponent + 1 := by
        obtain ⟨prior, hprior⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hexponent_pos)
        rw [hprior]
        simp [pow_succ]
      rw [padicValNat.eq_zero_of_not_dvd hnot_dvd]
  | first_merge =>
    refine ⟨1, by simp, ?_⟩
    simpa using (padicValNat.prime_pow (p := 2) 1)
  | right_open child_depth right_len count right_count cursor_open ih =>
    obtain ⟨units, hright_len, hcount⟩ := ih
    let exponent := child_depth - base_depth
    have hbase_le_child := right_count.base_le_depth
    have hcapacity : subtreeCapacity packing_factor child_depth =
        subtreeCapacity packing_factor base_depth * 2 ^ exponent := by
      exact subtreeCapacity_eq_mul_pow_of_le packing_factor hbase_le_child
    have hunits_lt : units + 1 < 2 ^ exponent := by
      apply (Nat.mul_lt_mul_left hbase_pos).mp
      simpa [hright_len, hcapacity, Nat.mul_add]
        using cursor_open
    have hvaluation_lt : padicValNat 2 (units + 1) < exponent := by
      by_contra hnot_lt
      have hpow_dvd : 2 ^ exponent ∣ units + 1 :=
        (pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd
      have hpow_le : 2 ^ exponent ≤ units + 1 :=
        Nat.le_of_dvd (by omega) hpow_dvd
      omega
    refine ⟨2 ^ exponent + units, ?_, ?_⟩
    · rw [hright_len, hcapacity]
      simp [Nat.mul_add]
    · rw [hcount]
      have hvaluation := padicValNat_two_pow_add_of_lt
        (exponent := exponent) (value := units + 1) (by omega)
        hvaluation_lt
      simpa [Nat.add_assoc] using hvaluation.symm
  | right_close child_depth right_len count right_count cursor_closes ih =>
    obtain ⟨units, hright_len, hcount⟩ := ih
    let exponent := child_depth - base_depth
    have hbase_le_child := right_count.base_le_depth
    have hcapacity : subtreeCapacity packing_factor child_depth =
        subtreeCapacity packing_factor base_depth * 2 ^ exponent := by
      exact subtreeCapacity_eq_mul_pow_of_le packing_factor hbase_le_child
    have hunits_eq : units + 1 = 2 ^ exponent := by
      apply Nat.mul_left_cancel hbase_pos
      simpa [hright_len, hcapacity, Nat.mul_add]
        using cursor_closes
    refine ⟨2 ^ exponent + units, ?_, ?_⟩
    · rw [hright_len, hcapacity]
      simp [Nat.mul_add]
    · have hsum : (2 ^ exponent + units) + 1 = 2 ^ (exponent + 1) := by
        rw [Nat.add_assoc, hunits_eq, pow_succ]
        omega
      rw [hcount, hunits_eq, padicValNat.prime_pow, hsum,
        padicValNat.prime_pow]

/-- Appending one nonempty dense subtree at the builder's base depth produces
    a merge plan and the canonical stack for the extended prefix. Alignment
    is the sole structural side condition: it says no earlier base subtree is
    partial. -/
theorem BuilderStack.append_subtree {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {root_depth total : Nat}
    (hstack : BuilderStack packing_factor base_depth stack root_depth total)
    {top : Tree T} {top_len : Nat}
    (htop : DenseTree packing_factor top base_depth top_len)
    (htop_nonempty : 0 < top_len)
    (haligned : total % subtreeCapacity packing_factor base_depth = 0)
    (hfits : total + top_len ≤
      subtreeCapacity packing_factor root_depth) :
    ∃ count final_stack final_top final_depth final_len,
      BuilderMergePlan ValueInst packing_factor count stack top final_stack
          final_top final_depth final_len ∧
        BuilderCarryCount packing_factor base_depth root_depth total count ∧
        BuilderStack packing_factor base_depth
          (final_stack ++ [utils.MaybeArced.Unarced final_top]) root_depth
          (total + top_len) ∧
        (total + subtreeCapacity packing_factor base_depth =
            subtreeCapacity packing_factor root_depth →
          final_stack = [] ∧ final_depth = root_depth ∧
            final_len = total + top_len) := by
  have hbase_pos := hlayout.subtreeCapacity_pos base_depth
  have htop_fit := htop.length_le_capacity
  induction hstack generalizing top top_len with
  | empty depth base_le_depth =>
    have hbase := BuilderStack.base (packing_factor := packing_factor)
      (utils.MaybeArced.Unarced top) top_len htop htop_nonempty
    have hraised := hbase.raise_left (depth - base_depth)
    have hdepth : base_depth + (depth - base_depth) = depth := by omega
    rw [hdepth] at hraised
    refine ⟨0, [], top, base_depth, top_len,
      BuilderMergePlan.done [] top base_depth top_len htop htop_nonempty,
      BuilderCarryCount.zero depth base_le_depth,
      by simpa using hraised, ?_⟩
    intro hfilled
    have hroot : base_depth = depth := by
      by_contra hne
      have hlt : base_depth < depth := by omega
      have hcap_lt := subtreeCapacity_strictMono hlayout hlt
      omega
    exact ⟨rfl, hroot, by simp⟩
  | base entry old_len old_dense old_nonempty =>
    have hold_bound := old_dense.length_le_capacity
    have hold_lt : old_len < subtreeCapacity packing_factor base_depth := by
      omega
    rw [Nat.mod_eq_of_lt hold_lt] at haligned
    omega
  | full entry depth base_le_depth dense capacity_nonempty =>
    omega
  | segment entry depth old_len base_le_depth dense nonempty
      full_or_unaligned =>
    rcases full_or_unaligned with hfull | hunaligned
    · omega
    · exact (hunaligned haligned).elim
  | @left child_stack child_depth child_len child_prefix child_fits ih =>
    by_cases hchild_full :
        child_len = subtreeCapacity packing_factor child_depth
    · obtain ⟨left, hsingle, hleft_dense⟩ :=
        child_prefix.full_single hlayout hchild_full
      subst child_stack
      by_cases hdepth_eq : base_depth = child_depth
      · subst child_depth
        obtain ⟨merged, hmerge, hmerged_dense⟩ :=
          node_unboxed_preserves_dense ValueInst (maybeArcedTree left) top
            base_depth (subtreeCapacity packing_factor base_depth) top_len
            hleft_dense htop (hlayout.subtreeCapacity_pos base_depth)
            (by intro; rfl)
        have hdone := BuilderMergePlan.done (ValueInst := ValueInst) [] merged
          (base_depth + 1)
          (subtreeCapacity packing_factor base_depth + top_len)
          hmerged_dense (by omega)
        have hplan := BuilderMergePlan.step [] left top merged base_depth top_len
          0 hleft_dense htop htop_nonempty hmerge hdone
        have hshape :
            subtreeCapacity packing_factor base_depth + top_len =
                subtreeCapacity packing_factor (base_depth + 1) ∨
              (subtreeCapacity packing_factor base_depth + top_len) %
                  subtreeCapacity packing_factor base_depth ≠ 0 := by
          by_cases htop_full :
              top_len = subtreeCapacity packing_factor base_depth
          · left
            rw [htop_full, subtreeCapacity_succ]
            simp [two_mul]
          · right
            have htop_lt : top_len <
                subtreeCapacity packing_factor base_depth := by omega
            rw [Nat.add_mod, Nat.mod_self, zero_add,
              Nat.mod_eq_of_lt htop_lt]
            simpa [Nat.mod_eq_of_lt htop_lt] using
              Nat.ne_of_gt htop_nonempty
        have hcanonical := BuilderStack.segment
          (packing_factor := packing_factor) (base_depth := base_depth)
          (utils.MaybeArced.Unarced merged) (base_depth + 1)
          (subtreeCapacity packing_factor base_depth + top_len) (by omega)
          hmerged_dense (by omega) hshape
        exact ⟨1, [], merged, base_depth + 1,
          subtreeCapacity packing_factor base_depth + top_len, by simpa using hplan,
          (by simpa [hchild_full] using
            (BuilderCarryCount.first_merge (packing_factor := packing_factor)
              (base_depth := base_depth))),
          by simpa [hchild_full] using hcanonical, by
            intro hfilled
            exact ⟨rfl, rfl, by simp [hchild_full]⟩⟩
      · have hdepth_lt : base_depth < child_depth := by
          have := child_prefix.base_le_depth
          omega
        have hcap_lt := subtreeCapacity_strictMono hlayout hdepth_lt
        have htop_lt :
            top_len < subtreeCapacity packing_factor child_depth := by omega
        have hright_base := BuilderStack.base (packing_factor := packing_factor)
          (utils.MaybeArced.Unarced top) top_len htop htop_nonempty
        have hright := hright_base.raise_left (child_depth - base_depth)
        have hdepth : base_depth + (child_depth - base_depth) = child_depth := by
          have := child_prefix.base_le_depth
          omega
        rw [hdepth] at hright
        have hcanonical := BuilderStack.right (base_depth := base_depth) left
          child_depth top_len hleft_dense hright htop_nonempty htop_lt
        have hplan := BuilderMergePlan.done (ValueInst := ValueInst) [left] top
          base_depth top_len htop htop_nonempty
        exact ⟨0, [left], top, base_depth, top_len, hplan,
          (by simpa [hchild_full] using
            (BuilderCarryCount.enter_right (packing_factor := packing_factor)
              child_depth hdepth_lt)),
          by simpa [hchild_full] using hcanonical, by
            intro hfilled
            rw [subtreeCapacity_succ] at hfilled
            omega⟩
    · have hchild_lt :
          child_len < subtreeCapacity packing_factor child_depth := by omega
      have hbase_dvd_child :
          subtreeCapacity packing_factor base_depth ∣
            subtreeCapacity packing_factor child_depth := by
        rw [subtreeCapacity_eq_mul_pow_of_le packing_factor
          child_prefix.base_le_depth]
        exact dvd_mul_right _ _
      have hchild_aligned :
          subtreeCapacity packing_factor child_depth %
            subtreeCapacity packing_factor base_depth = 0 :=
        Nat.mod_eq_zero_of_dvd hbase_dvd_child
      have hchild_sum : child_len + top_len ≤
          subtreeCapacity packing_factor child_depth :=
        aligned_add_le hbase_pos haligned hchild_aligned hchild_lt htop_fit
      obtain ⟨count, final_stack, final_top, final_depth, final_len,
          hplan, hcarry, hcanonical, hcursor⟩ :=
        ih htop htop_nonempty haligned hchild_sum htop_fit
      exact ⟨count, final_stack, final_top, final_depth, final_len, hplan,
        BuilderCarryCount.inside child_depth child_len count hcarry hchild_lt,
        BuilderStack.left hcanonical hcanonical.length_le_capacity, by
          intro hfilled
          rw [subtreeCapacity_succ] at hfilled
          have hbase_le_child :
              subtreeCapacity packing_factor base_depth ≤
                subtreeCapacity packing_factor child_depth := by
            exact Nat.le_of_dvd (hlayout.subtreeCapacity_pos child_depth)
              hbase_dvd_child
          omega⟩
  | @right left right_stack child_depth right_len left_dense right_prefix
      right_nonempty right_not_full ih =>
    have hbase_dvd_child :
        subtreeCapacity packing_factor base_depth ∣
          subtreeCapacity packing_factor child_depth := by
      rw [subtreeCapacity_eq_mul_pow_of_le packing_factor
        right_prefix.base_le_depth]
      exact dvd_mul_right _ _
    have htotal_dvd : subtreeCapacity packing_factor base_depth ∣
        subtreeCapacity packing_factor child_depth + right_len :=
      Nat.dvd_of_mod_eq_zero haligned
    have hright_dvd :
        subtreeCapacity packing_factor base_depth ∣ right_len := by
      have hsub := Nat.dvd_sub htotal_dvd hbase_dvd_child
      simpa using hsub
    have hright_aligned :
        right_len % subtreeCapacity packing_factor base_depth = 0 :=
      Nat.mod_eq_zero_of_dvd hright_dvd
    have hright_sum : right_len + top_len ≤
        subtreeCapacity packing_factor child_depth := by
      rw [subtreeCapacity_succ] at hfits
      omega
    obtain ⟨count, final_stack, final_top, final_depth, final_len,
        hplan, hcarry, hright_canonical, hcursor⟩ :=
      ih htop htop_nonempty hright_aligned hright_sum htop_fit
    by_cases hcursor_full : right_len +
        subtreeCapacity packing_factor base_depth =
        subtreeCapacity packing_factor child_depth
    · obtain ⟨hfinal_stack, hfinal_depth, hfinal_len⟩ :=
        hcursor hcursor_full
      subst final_stack
      subst final_depth
      have hright_dense := hplan.final_dense
      rw [hfinal_len] at hright_dense
      obtain ⟨merged, hmerge, hmerged_dense⟩ :=
        node_unboxed_preserves_dense ValueInst (maybeArcedTree left) final_top
          child_depth (subtreeCapacity packing_factor child_depth)
          (right_len + top_len) left_dense hright_dense
          (hlayout.subtreeCapacity_pos child_depth) (by intro; rfl)
      have hdone := BuilderMergePlan.done (ValueInst := ValueInst) [] merged
        (child_depth + 1)
        (subtreeCapacity packing_factor child_depth + (right_len + top_len))
        hmerged_dense (by omega)
      have hlast := BuilderMergePlan.step [] left final_top merged child_depth
        (right_len + top_len) 0 left_dense hright_dense (by omega) hmerge hdone
      have hfirst := hplan.prepend [left]
      have hcombined := hfirst.trans hlast
      have hchild_aligned : subtreeCapacity packing_factor child_depth %
          subtreeCapacity packing_factor base_depth = 0 :=
        Nat.mod_eq_zero_of_dvd hbase_dvd_child
      have hshape :
          subtreeCapacity packing_factor child_depth + (right_len + top_len) =
              subtreeCapacity packing_factor (child_depth + 1) ∨
            (subtreeCapacity packing_factor child_depth +
                (right_len + top_len)) %
                subtreeCapacity packing_factor base_depth ≠ 0 := by
        by_cases htop_full :
            top_len = subtreeCapacity packing_factor base_depth
        · left
          rw [subtreeCapacity_succ]
          simp [two_mul]
          omega
        · right
          have htop_lt : top_len <
              subtreeCapacity packing_factor base_depth := by omega
          rw [Nat.add_mod, hchild_aligned, zero_add, Nat.add_mod,
            hright_aligned, zero_add, Nat.mod_eq_of_lt htop_lt,
            Nat.mod_eq_of_lt htop_lt]
          simpa [Nat.mod_eq_of_lt htop_lt] using
            Nat.ne_of_gt htop_nonempty
      have hcanonical := BuilderStack.segment (packing_factor := packing_factor)
        (base_depth := base_depth) (utils.MaybeArced.Unarced merged)
        (child_depth + 1)
        (subtreeCapacity packing_factor child_depth + (right_len + top_len))
        (by have := right_prefix.base_le_depth; omega) hmerged_dense (by omega)
        hshape
      exact ⟨count + 1, [], merged, child_depth + 1,
        subtreeCapacity packing_factor child_depth + (right_len + top_len),
        hcombined, BuilderCarryCount.right_close child_depth right_len count
          hcarry hcursor_full,
        by simpa [Nat.add_assoc] using hcanonical, by
          intro hfilled
          exact ⟨rfl, rfl, by simp [Nat.add_assoc]⟩⟩
    · have hchild_aligned : subtreeCapacity packing_factor child_depth %
          subtreeCapacity packing_factor base_depth = 0 :=
        Nat.mod_eq_zero_of_dvd hbase_dvd_child
      have hcursor_le : right_len +
          subtreeCapacity packing_factor base_depth ≤
          subtreeCapacity packing_factor child_depth :=
        aligned_add_le hbase_pos hright_aligned hchild_aligned right_not_full
          (Nat.le_refl _)
      have hnew_nonempty : 0 < right_len + top_len := by omega
      have hnew_lt : right_len + top_len <
          subtreeCapacity packing_factor child_depth := by
        by_contra hnot_lt
        have hnew_eq : right_len + top_len =
            subtreeCapacity packing_factor child_depth := by omega
        have htop_full : top_len =
            subtreeCapacity packing_factor base_depth := by omega
        exact hcursor_full (by omega)
      have hcanonical := BuilderStack.right (base_depth := base_depth) left
        child_depth (right_len + top_len) left_dense hright_canonical
        hnew_nonempty hnew_lt
      exact ⟨count, [left] ++ final_stack, final_top, final_depth, final_len,
        hplan.prepend [left], BuilderCarryCount.right_open child_depth right_len
          count hcarry (by omega),
        by simpa [Nat.add_assoc] using hcanonical, by
          intro hfilled
          rw [subtreeCapacity_succ] at hfilled
          omega⟩

/-- Appending a partial base subtree performs no carry: the new subtree is
    simply the last stack entry. This is the packed-value path before the
    current packed leaf reaches its factor. -/
theorem BuilderStack.append_partial {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {root_depth total : Nat}
    (hstack : BuilderStack packing_factor base_depth stack root_depth total)
    {top : utils.MaybeArced (Tree T)} {top_len : Nat}
    (htop : DenseTree packing_factor (maybeArcedTree top) base_depth top_len)
    (htop_nonempty : 0 < top_len)
    (htop_partial : top_len < subtreeCapacity packing_factor base_depth)
    (haligned : total % subtreeCapacity packing_factor base_depth = 0)
    (hfits : total + top_len ≤
      subtreeCapacity packing_factor root_depth) :
    BuilderStack packing_factor base_depth (stack ++ [top]) root_depth
      (total + top_len) := by
  have hbase_pos := hlayout.subtreeCapacity_pos base_depth
  induction hstack with
  | empty depth base_le_depth =>
    have hbase := BuilderStack.base (packing_factor := packing_factor) top
      top_len htop htop_nonempty
    have hraised := hbase.raise_left (depth - base_depth)
    have hdepth : base_depth + (depth - base_depth) = depth := by omega
    rw [hdepth] at hraised
    simpa using hraised
  | base entry old_len old_dense old_nonempty =>
    have hold_bound := old_dense.length_le_capacity
    have hold_lt : old_len < subtreeCapacity packing_factor base_depth := by
      omega
    rw [Nat.mod_eq_of_lt hold_lt] at haligned
    omega
  | full entry depth base_le_depth dense capacity_nonempty =>
    omega
  | segment entry depth old_len base_le_depth dense nonempty
      full_or_unaligned =>
    rcases full_or_unaligned with hfull | hunaligned
    · omega
    · exact (hunaligned haligned).elim
  | @left child_stack child_depth child_len child_prefix child_fits ih =>
    by_cases hchild_full :
        child_len = subtreeCapacity packing_factor child_depth
    · obtain ⟨left, hsingle, hleft_dense⟩ :=
        child_prefix.full_single hlayout hchild_full
      subst child_stack
      have hbase_le_child := child_prefix.base_le_depth
      have htop_child_lt : top_len <
          subtreeCapacity packing_factor child_depth := by
        by_cases hdepth : base_depth = child_depth
        · simpa [hdepth] using htop_partial
        · exact (htop_partial.trans_le
            (Nat.le_of_lt (subtreeCapacity_strictMono hlayout (by omega))))
      have hright_base := BuilderStack.base (packing_factor := packing_factor)
        top top_len htop htop_nonempty
      have hright := hright_base.raise_left (child_depth - base_depth)
      have hdepth : base_depth + (child_depth - base_depth) = child_depth := by
        omega
      rw [hdepth] at hright
      have hcanonical := BuilderStack.right (base_depth := base_depth) left
        child_depth top_len hleft_dense hright htop_nonempty htop_child_lt
      simpa [hchild_full] using hcanonical
    · have hchild_lt :
          child_len < subtreeCapacity packing_factor child_depth := by omega
      have hbase_dvd_child :
          subtreeCapacity packing_factor base_depth ∣
            subtreeCapacity packing_factor child_depth := by
        rw [subtreeCapacity_eq_mul_pow_of_le packing_factor
          child_prefix.base_le_depth]
        exact dvd_mul_right _ _
      have hchild_aligned :
          subtreeCapacity packing_factor child_depth %
            subtreeCapacity packing_factor base_depth = 0 :=
        Nat.mod_eq_zero_of_dvd hbase_dvd_child
      have hchild_sum : child_len + top_len ≤
          subtreeCapacity packing_factor child_depth :=
        aligned_add_le hbase_pos haligned hchild_aligned hchild_lt
          (Nat.le_of_lt htop_partial)
      have hchild_appended := ih haligned hchild_sum
      exact BuilderStack.left hchild_appended
        hchild_appended.length_le_capacity
  | @right left right_stack child_depth right_len left_dense right_prefix
      right_nonempty right_not_full ih =>
    have hbase_dvd_child :
        subtreeCapacity packing_factor base_depth ∣
          subtreeCapacity packing_factor child_depth := by
      rw [subtreeCapacity_eq_mul_pow_of_le packing_factor
        right_prefix.base_le_depth]
      exact dvd_mul_right _ _
    have htotal_dvd : subtreeCapacity packing_factor base_depth ∣
        subtreeCapacity packing_factor child_depth + right_len :=
      Nat.dvd_of_mod_eq_zero haligned
    have hright_dvd :
        subtreeCapacity packing_factor base_depth ∣ right_len := by
      have hsub := Nat.dvd_sub htotal_dvd hbase_dvd_child
      simpa using hsub
    have hright_aligned :
        right_len % subtreeCapacity packing_factor base_depth = 0 :=
      Nat.mod_eq_zero_of_dvd hright_dvd
    have hchild_aligned : subtreeCapacity packing_factor child_depth %
        subtreeCapacity packing_factor base_depth = 0 :=
      Nat.mod_eq_zero_of_dvd hbase_dvd_child
    have hcursor_le : right_len +
        subtreeCapacity packing_factor base_depth ≤
        subtreeCapacity packing_factor child_depth :=
      aligned_add_le hbase_pos hright_aligned hchild_aligned right_not_full
        (Nat.le_refl _)
    have hright_sum : right_len + top_len <
        subtreeCapacity packing_factor child_depth := by omega
    have hright_appended := ih hright_aligned (Nat.le_of_lt hright_sum)
    have hcanonical := BuilderStack.right (base_depth := base_depth) left
      child_depth (right_len + top_len) left_dense hright_appended (by omega)
      hright_sum
    simpa [List.append_assoc, Nat.add_assoc] using hcanonical

/-- Removing a known partial base subtree from the end of a canonical stack
    leaves an aligned canonical prefix. The explicit final-entry equation is
    exactly what a successful translated `Vec::pop` supplies. -/
theorem BuilderStack.remove_partial_last {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat}
    {stack base_stack : List (utils.MaybeArced (Tree T))}
    {entry : utils.MaybeArced (Tree T)}
    {root_depth total entry_len : Nat}
    (hstack : BuilderStack packing_factor base_depth stack root_depth total)
    (hentries : stack = base_stack ++ [entry])
    (hentry : DenseTree packing_factor (maybeArcedTree entry) base_depth
      entry_len)
    (hentry_nonempty : 0 < entry_len)
    (hentry_partial : entry_len <
      subtreeCapacity packing_factor base_depth) :
    ∃ prefix_len,
      total = prefix_len + entry_len ∧
        prefix_len % subtreeCapacity packing_factor base_depth = 0 ∧
        BuilderStack packing_factor base_depth base_stack root_depth prefix_len := by
  have hbase_pos := hlayout.subtreeCapacity_pos base_depth
  induction hstack generalizing base_stack with
  | empty depth base_le_depth =>
    simp at hentries
  | base old_entry old_len old_dense old_nonempty =>
    have hprefix_length := congrArg List.length hentries
    have hprefix_empty : base_stack = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hprefix_length
    subst base_stack
    simp at hentries
    subst old_entry
    obtain ⟨-, hlen⟩ := old_dense.indices_unique hentry
    refine ⟨0, by omega, by simp, ?_⟩
    exact BuilderStack.empty base_depth (Nat.le_refl _)
  | full old_entry depth base_le_depth old_dense capacity_nonempty =>
    have hprefix_length := congrArg List.length hentries
    have hprefix_empty : base_stack = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hprefix_length
    subst base_stack
    simp at hentries
    subst old_entry
    obtain ⟨hdepth, hlen⟩ := old_dense.indices_unique hentry
    subst depth
    omega
  | segment old_entry depth old_len base_le_depth old_dense old_nonempty
      full_or_unaligned =>
    have hprefix_length := congrArg List.length hentries
    have hprefix_empty : base_stack = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hprefix_length
    subst base_stack
    simp at hentries
    subst old_entry
    obtain ⟨hdepth, hlen⟩ := old_dense.indices_unique hentry
    subst depth
    refine ⟨0, by omega, by simp, ?_⟩
    exact BuilderStack.empty base_depth (Nat.le_refl _)
  | @left child_stack child_depth child_len child_prefix child_fits ih =>
    obtain ⟨prefix_len, htotal, haligned, hprefix⟩ :=
      ih hentries
    exact ⟨prefix_len, htotal, haligned,
      BuilderStack.left hprefix hprefix.length_le_capacity⟩
  | @right left right_stack child_depth right_len left_dense right_prefix
      right_nonempty right_not_full ih =>
    have hright_nonempty : right_stack ≠ [] :=
      right_prefix.ne_nil_of_length_pos right_nonempty
    cases base_stack with
    | nil =>
      simp at hentries
      exact (hright_nonempty hentries.2).elim
    | cons prefix_head prefix_tail =>
      simp only [List.cons_append, List.cons.injEq] at hentries
      obtain ⟨rfl, hright_entries⟩ := hentries
      obtain ⟨right_prefix_len, hright_total, hright_aligned,
          hright_prefix⟩ := ih hright_entries
      have hbase_dvd_child :
          subtreeCapacity packing_factor base_depth ∣
            subtreeCapacity packing_factor child_depth := by
        rw [subtreeCapacity_eq_mul_pow_of_le packing_factor
          right_prefix.base_le_depth]
        exact dvd_mul_right _ _
      have hchild_aligned : subtreeCapacity packing_factor child_depth %
          subtreeCapacity packing_factor base_depth = 0 :=
        Nat.mod_eq_zero_of_dvd hbase_dvd_child
      by_cases hprefix_zero : right_prefix_len = 0
      · subst right_prefix_len
        have htail_empty := hright_prefix.eq_nil_of_length_zero rfl
        subst prefix_tail
        have hleft_stack := BuilderStack.full
          (packing_factor := packing_factor) (base_depth := base_depth) left
          child_depth right_prefix.base_le_depth left_dense
          (hlayout.subtreeCapacity_pos child_depth)
        have hleft_parent := BuilderStack.left hleft_stack
          (Nat.le_refl _)
        refine ⟨subtreeCapacity packing_factor child_depth, ?_,
          hchild_aligned, by simpa using hleft_parent⟩
        omega
      · have hprefix_pos : 0 < right_prefix_len := Nat.pos_of_ne_zero
          hprefix_zero
        have hprefix_lt : right_prefix_len <
            subtreeCapacity packing_factor child_depth := by omega
        have hparent := BuilderStack.right (base_depth := base_depth) left
          child_depth right_prefix_len left_dense hright_prefix hprefix_pos
          hprefix_lt
        refine ⟨subtreeCapacity packing_factor child_depth +
            right_prefix_len, ?_, ?_, by simpa using hparent⟩
        · omega
        · rw [Nat.add_mod, hchild_aligned, hright_aligned]
          rfl

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

private theorem push_node_loop_step {T : Type} (ValueInst : Value T)
    (iter : core.ops.range.Range Std.U32)
    (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
    (top : utils.MaybeArced (Tree T)) :
    builder.Builder.push_node_loop ValueInst iter stack top =
      match builder.Builder.push_node_loop.body ValueInst iter stack top with
      | ok (.cont (iter1, stack1, top1)) =>
        builder.Builder.push_node_loop ValueInst iter1 stack1 top1
      | ok (.done result) => ok result
      | fail error => fail error
      | div => div := by
  conv_lhs => unfold builder.Builder.push_node_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hbody : builder.Builder.push_node_loop.body ValueInst iter stack top with
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
    {final_top : Tree T} {final_depth final_len : Nat}
    (hplan : BuilderMergePlan ValueInst packing_factor count input_stack
      input_top final_stack final_top final_depth final_len) :
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
  | done plan_stack top depth top_len top_dense top_nonempty =>
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
  | @step base_stack left top merged depth top_len remaining_count final_stack
      final_top final_depth final_len left_dense top_dense top_nonempty merge_eq
      remaining ih =>
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

private theorem push_node_loop_follows_merge_plan {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {count : Nat} {input_stack : List (utils.MaybeArced (Tree T))}
    {input_top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth final_len : Nat}
    (hplan : BuilderMergePlan ValueInst packing_factor count input_stack
      input_top final_stack final_top final_depth final_len) :
    ∀ (iter : core.ops.range.Range Std.U32)
      (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
      (top : utils.MaybeArced (Tree T))
      (result_stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
      (result_top : utils.MaybeArced (Tree T)),
      iter.end.val = iter.start.val + count →
      stack.val = input_stack →
      maybeArcedTree top = input_top →
      builder.Builder.push_node_loop ValueInst iter stack top =
        ok (result_stack, result_top) →
      result_stack.val = final_stack ∧
        maybeArcedTree result_top = final_top := by
  induction hplan with
  | done plan_stack plan_top depth len top_dense top_nonempty =>
    intro iter stack top result_stack result_top hremaining hstack htop hloop
    have hge : iter.start.val ≥ iter.end.val := by omega
    have hnext := range_u32_next_none iter hge
    rw [push_node_loop_step] at hloop
    unfold builder.Builder.push_node_loop.body at hloop
    simp only [hnext, bind_tc_ok] at hloop
    obtain ⟨rfl, rfl⟩ := hloop
    exact ⟨hstack, htop⟩
  | @step base_stack left plan_top merged depth top_len remaining_count
      final_stack final_top final_depth final_len left_dense top_dense
      top_nonempty merge_eq remaining ih =>
    intro iter stack top result_stack result_top hremaining hstack htop hloop
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
    rw [push_node_loop_step] at hloop
    unfold builder.Builder.push_node_loop.body at hloop
    simp [hnext, hpop, maybeArced_arced, htop, merge_eq] at hloop
    apply ih iter1 rest (utils.MaybeArced.Unarced merged) result_stack
      result_top
    · have hend_value := congrArg UScalar.val hend
      omega
    · exact hrest
    · rfl
    · exact hloop

private theorem PackingLayout.packing_depth_zero_of_none {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hfactor : packing_factor = none) : packing_depth.val = 0 := by
  cases hlayout with
  | unpacked => rfl
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    simp at hfactor

private theorem push_full_base_merge_count_eq {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {root_depth total count : Nat}
    (hcarry : BuilderCarryCount packing_factor 0 root_depth total count)
    {next_index : Std.Usize} {zeros : Std.U32}
    (hnext : next_index.val = total + subtreeCapacity packing_factor 0)
    (hzeros : core.num.Usize.trailing_zeros next_index = ok zeros) :
    (core.num.U32.saturating_sub zeros
      (UScalar.cast .U32 packing_depth)).val = count := by
  obtain ⟨units, htotal, hcount⟩ := hcarry.eq_padic_units hlayout
  have hcapacity := hlayout.subtreeCapacity_eq_two_pow 0
  have hnext_units : next_index.val =
      2 ^ packing_depth.val * (units + 1) := by
    rw [hnext, htotal, hcapacity]
    simp [Nat.mul_add]
  have hnext_pos : 0 < next_index.val := by
    rw [hnext_units]
    positivity
  have hzero_value := usize_trailing_zeros_padic hnext_pos hzeros
  rw [u32_saturating_sub_value,
    hlayout.packing_depth_cast_u32, hzero_value, hnext_units,
    padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    hcount]
  omega

private theorem push_partial_base_merge_count_zero {T : Type}
    {ValueInst : Value T} {factor packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst (some factor) packing_depth)
    {next_index : Std.Usize} {zeros : Std.U32}
    (hnext_pos : 0 < next_index.val)
    (hpartial : next_index.val % factor.val ≠ 0)
    (hzeros : core.num.Usize.trailing_zeros next_index = ok zeros) :
    (core.num.U32.saturating_sub zeros
      (UScalar.cast .U32 packing_depth)).val = 0 := by
  have hfactor := hlayout.subtreeCapacity_eq_two_pow 0
  simp [subtreeCapacity, leafCapacity] at hfactor
  have hnot_dvd : ¬2 ^ packing_depth.val ∣ next_index.val := by
    rw [← hfactor]
    exact fun hdvd => hpartial (Nat.mod_eq_zero_of_dvd hdvd)
  have hvaluation_lt :
      padicValNat 2 next_index.val < packing_depth.val := by
    by_contra hnot_lt
    have hdvd : 2 ^ packing_depth.val ∣ next_index.val :=
      (pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd
    exact hnot_dvd hdvd
  rw [u32_saturating_sub_value,
    hlayout.packing_depth_cast_u32,
    usize_trailing_zeros_padic hnext_pos hzeros]
  omega

private theorem push_node_merge_count_eq {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    (hinvariant : BuilderInvariant ValueInst self)
    (hnode_level : self.level.val ≠ 0 ∨ self.packing_factor = none)
    {count : Nat}
    (hcarry : BuilderCarryCount self.packing_factor
      (if self.level.val = 0 then 0
        else self.level.val - self.packing_depth.val)
      self.depth.val self.length.val count)
    {index_on_level next_index_on_level : Std.Usize}
    (hshift : self.length >>> self.level = ok index_on_level)
    (hnext : index_on_level + 1#usize = ok next_index_on_level)
    {values_to_merge : Std.U32}
    (hvalues :
      (if self.level = 0#usize then
        do
          let zeros ← core.num.Usize.trailing_zeros next_index_on_level
          let packing_depth ← lift (UScalar.cast .U32 self.packing_depth)
          ok (core.num.U32.saturating_sub zeros packing_depth)
      else core.num.Usize.trailing_zeros next_index_on_level) =
        ok values_to_merge) :
    values_to_merge.val = count := by
  obtain ⟨units, hlength, hcount⟩ :=
    hcarry.eq_padic_units (BuilderInvariant.layout hinvariant)
  have hbase := hinvariant.base_capacity_eq_pow_level hnode_level
  have hindex := usize_shift_right_value hshift
  have hindex_units : index_on_level.val = units := by
    rw [Nat.shiftRight_eq_div_pow, hlength, hbase] at hindex
    simpa using hindex
  have hnext_value := usize_add_one_value hnext
  have hnext_units : next_index_on_level.val = units + 1 := by omega
  have hnext_pos : 0 < next_index_on_level.val := by omega
  by_cases hlevel : self.level.val = 0
  · have hlevel_scalar : self.level = 0#usize :=
      UScalar.eq_of_val_eq (by simpa using hlevel)
    have hfactor : self.packing_factor = none := hnode_level.resolve_left
      (not_not.mpr hlevel)
    have hpacking_depth :=
      (BuilderInvariant.layout hinvariant).packing_depth_zero_of_none hfactor
    rw [if_pos hlevel_scalar] at hvalues
    cases hzeros : core.num.Usize.trailing_zeros next_index_on_level with
    | fail error => simp [hzeros] at hvalues
    | div => simp [hzeros] at hvalues
    | ok zeros =>
      simp [hzeros, lift] at hvalues
      subst values_to_merge
      rw [u32_saturating_sub_value]
      have hcast : (UScalar.cast .U32 self.packing_depth).val = 0 := by
        rw [UScalar.cast_val_eq, hpacking_depth]
        simp
      rw [hcast, Nat.sub_zero,
        usize_trailing_zeros_padic hnext_pos hzeros, hnext_units]
      exact hcount.symm
  · have hlevel_scalar : self.level ≠ 0#usize := by
      intro heq
      apply hlevel
      exact congrArg UScalar.val heq
    rw [if_neg hlevel_scalar] at hvalues
    rw [usize_trailing_zeros_padic hnext_pos hvalues, hnext_units]
    exact hcount.symm

/-- Successful internal-node insertion preserves the canonical Builder stack.
    The three premises beyond the invariant are exactly the caller protocol:
    `push_node` is not used for packed level zero, the supplied node describes
    its reported logical length, and the current cursor starts on a level
    boundary. Capacity and machine-arithmetic facts follow from success. -/
theorem builder_push_node_preserves_invariant {T : Type}
    {ValueInst : Value T} {self result : builder.Builder T}
    (hinvariant : BuilderInvariant ValueInst self)
    (hnode_level : self.level.val ≠ 0 ∨ self.packing_factor = none)
    (node : triomphe.arc.Arc (Tree T)) (len : Std.Usize)
    (hnode : DenseTree self.packing_factor node
      (if self.level.val = 0 then 0
        else self.level.val - self.packing_depth.val) len.val)
    (hlen : 0 < len.val)
    (haligned : self.length.val % subtreeCapacity self.packing_factor
      (if self.level.val = 0 then 0
        else self.level.val - self.packing_depth.val) = 0)
    (hpush : builder.Builder.push_node ValueInst self node len =
      ok (core.result.Result.Ok (), result)) :
    BuilderInvariant ValueInst result := by
  unfold builder.Builder.push_node at hpush
  simp only [utils.Length.as_usize, bind_tc_ok] at hpush
  cases hchecked : Usize.checked_add self.length len with
  | none =>
    rw [hchecked] at hpush
    simp [lift] at hpush
  | some new_length =>
    rw [hchecked] at hpush
    simp only [lift, bind_tc_ok] at hpush
    by_cases hgreater : new_length > self.capacity
    · rw [if_pos hgreater] at hpush
      simp at hpush
    · rw [if_neg hgreater] at hpush
      cases hshift : self.length >>> self.level with
      | fail error => simp [hshift] at hpush
      | div => simp [hshift] at hpush
      | ok index_on_level =>
        simp only [hshift, bind_tc_ok] at hpush
        cases hnext : index_on_level + 1#usize with
        | fail error => simp [hnext] at hpush
        | div => simp [hnext] at hpush
        | ok next_index_on_level =>
          simp only [hnext, bind_tc_ok] at hpush
          cases hvalues :
              (if self.level = 0#usize then
                do
                  let zeros ←
                    core.num.Usize.trailing_zeros next_index_on_level
                  ok (core.num.U32.saturating_sub zeros
                    (UScalar.cast .U32 self.packing_depth))
              else core.num.Usize.trailing_zeros next_index_on_level) with
          | fail error => simp [hvalues] at hpush
          | div => simp [hvalues] at hpush
          | ok values_to_merge =>
            simp only [hvalues, bind_tc_ok] at hpush
            cases hloop : builder.Builder.push_node_loop ValueInst
                { start := 0#u32, «end» := values_to_merge } self.stack
                (utils.MaybeArced.Arced node) with
            | fail error => simp [hloop] at hpush
            | div => simp [hloop] at hpush
            | ok loop_result =>
              obtain ⟨loop_stack, loop_top⟩ := loop_result
              simp only [hloop, bind_tc_ok] at hpush
              cases hstack_push : alloc.vec.Vec.push loop_stack loop_top with
              | fail error => simp [hstack_push] at hpush
              | div => simp [hstack_push] at hpush
              | ok final_stack =>
                simp [hstack_push, utils.Length.as_mut] at hpush
                subst result
                have hnew_length := usize_checked_add_value hchecked
                have hnew_le : new_length.val ≤ self.capacity.val := by
                  scalar_tac
                have hfits : self.length.val + len.val ≤
                    subtreeCapacity self.packing_factor self.depth.val := by
                  rw [← hnew_length,
                    ← BuilderInvariant.builder_capacity_matches hinvariant]
                  exact hnew_le
                obtain ⟨count, plan_stack, plan_top, plan_depth, plan_len,
                    hplan, hcarry, hcanonical, _⟩ :=
                  BuilderStack.append_subtree
                    (BuilderInvariant.layout hinvariant)
                    (BuilderInvariant.stack_dense hinvariant) hnode hlen
                    haligned hfits
                have hvalues_full :
                    (if self.level = 0#usize then
                      do
                        let zeros ← core.num.Usize.trailing_zeros
                          next_index_on_level
                        let packing_depth ←
                          lift (UScalar.cast .U32 self.packing_depth)
                        ok (core.num.U32.saturating_sub zeros packing_depth)
                    else core.num.Usize.trailing_zeros next_index_on_level) =
                      ok values_to_merge := by
                  simpa only [lift, bind_tc_ok] using hvalues
                have hmerge_count := push_node_merge_count_eq hinvariant
                  hnode_level hcarry hshift hnext hvalues_full
                obtain ⟨hloop_stack, hloop_top⟩ :=
                  push_node_loop_follows_merge_plan hplan
                    { start := 0#u32, «end» := values_to_merge }
                    self.stack (utils.MaybeArced.Arced node) loop_stack
                    loop_top (by simp [hmerge_count]) rfl rfl hloop
                have hfinal_stack := vec_push_values loop_stack loop_top
                  hstack_push
                have hcanonical_final : BuilderStack self.packing_factor
                    (if self.level.val = 0 then 0
                      else self.level.val - self.packing_depth.val)
                    final_stack.val self.depth.val
                    (self.length.val + len.val) := by
                  apply hcanonical.rewrap
                  rw [hfinal_stack, hloop_stack]
                  simp [hloop_top]
                refine ⟨@BuilderInvariant.layout T ValueInst self hinvariant,
                  @BuilderInvariant.level_valid T ValueInst self hinvariant,
                  @BuilderInvariant.level_bounded T ValueInst self hinvariant,
                  @BuilderInvariant.builder_capacity_matches T ValueInst self
                    hinvariant, ?_⟩
                simpa [hnew_length] using hcanonical_final

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
