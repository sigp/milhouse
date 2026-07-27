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
      (full_or_final_partial :
        len = subtreeCapacity packing_factor depth ∨
          (subtreeCapacity packing_factor depth -
              subtreeCapacity packing_factor base_depth < len ∧
            len % subtreeCapacity packing_factor base_depth ≠ 0)) :
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

/-- A carry-normalized view of a Builder stack. `physical_len` counts the
    base-capacity slots occupied by the stack, while `logical_len` counts only
    materialized values. A partial final subtree therefore occupies its full
    physical capacity. -/
inductive BuilderNormalizedStack {T : Type}
    (packing_factor : Option Std.Usize) (base_depth : Nat) :
    List (utils.MaybeArced (Tree T)) → Nat → Nat → Nat → Prop where
  | empty (depth : Nat) (base_le_depth : base_depth ≤ depth) :
      BuilderNormalizedStack packing_factor base_depth [] depth 0 0
  | single (entry : utils.MaybeArced (Tree T)) (depth len : Nat)
      (base_le_depth : base_depth ≤ depth)
      (dense : DenseTree packing_factor (maybeArcedTree entry) depth len)
      (nonempty : 0 < len) :
      BuilderNormalizedStack packing_factor base_depth [entry] depth len
        (subtreeCapacity packing_factor depth)
  | left {stack : List (utils.MaybeArced (Tree T))}
      {depth logical_len physical_len : Nat}
      (child : BuilderNormalizedStack packing_factor base_depth stack depth
        logical_len physical_len)
      (physical_fits : physical_len ≤
        subtreeCapacity packing_factor depth) :
      BuilderNormalizedStack packing_factor base_depth stack (depth + 1)
        logical_len physical_len
  | right (left : utils.MaybeArced (Tree T))
      {right_stack : List (utils.MaybeArced (Tree T))}
      (depth right_logical right_physical : Nat)
      (left_dense : DenseTree packing_factor (maybeArcedTree left) depth
        (subtreeCapacity packing_factor depth))
      (right : BuilderNormalizedStack packing_factor base_depth right_stack
        depth right_logical right_physical)
      (right_nonempty : 0 < right_logical)
      (right_physical_not_full : right_physical <
        subtreeCapacity packing_factor depth) :
      BuilderNormalizedStack packing_factor base_depth (left :: right_stack)
        (depth + 1) (subtreeCapacity packing_factor depth + right_logical)
        (subtreeCapacity packing_factor depth + right_physical)

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
  | segment entry depth len base_le_depth dense nonempty full_or_final_partial =>
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
  | segment entry depth len base_le_depth dense nonempty full_or_final_partial =>
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

theorem BuilderNormalizedStack.physical_le_capacity {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth stack root_depth
      logical_len physical_len) :
    physical_len ≤ subtreeCapacity packing_factor root_depth := by
  induction h with
  | empty => simp
  | single => exact Nat.le_refl _
  | left child physical_fits ih =>
    rw [subtreeCapacity_succ]
    omega
  | right left depth right_logical right_physical left_dense right
      right_nonempty right_physical_not_full ih =>
    rw [subtreeCapacity_succ]
    omega

theorem BuilderNormalizedStack.base_le_depth {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth stack root_depth
      logical_len physical_len) : base_depth ≤ root_depth := by
  induction h with
  | empty depth base_le_depth => exact base_le_depth
  | single entry depth len base_le_depth dense nonempty => exact base_le_depth
  | left child physical_fits ih => omega
  | right left depth right_logical right_physical left_dense right
      right_nonempty right_physical_not_full ih => omega

private theorem BuilderStack.eq_nil_of_length_zero_early {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len)
    (hzero : len = 0) : stack = [] := by
  induction h with
  | empty => rfl
  | base entry len dense nonempty => omega
  | full entry depth base_le_depth dense capacity_nonempty => omega
  | segment entry depth len base_le_depth dense nonempty full_or_final_partial =>
    omega
  | left child_prefix fits_left ih => exact ih hzero
  | right left depth right_len left_dense right_prefix
      right_nonempty right_not_full ih => omega

theorem BuilderNormalizedStack.ne_nil_of_logical_pos {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth stack root_depth
      logical_len physical_len) (hpos : 0 < logical_len) : stack ≠ [] := by
  induction h with
  | empty => omega
  | single => simp
  | left child physical_fits ih => exact ih hpos
  | right => simp

/-- A normalized stack that occupies the root capacity and has one entry is
    already the finished dense root. -/
theorem BuilderNormalizedStack.singleton_dense_of_full_physical {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat} {entry : utils.MaybeArced (Tree T)}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth [entry] root_depth
      logical_len physical_len)
    (hphysical : physical_len = subtreeCapacity packing_factor root_depth) :
    DenseTree packing_factor (maybeArcedTree entry) root_depth logical_len := by
  cases h with
  | single entry depth len base_le_depth dense nonempty => exact dense
  | @left stack child_depth child_logical child_physical child physical_fits =>
    rw [subtreeCapacity_succ] at hphysical
    have hpos := hlayout.subtreeCapacity_pos child_depth
    omega
  | @right left right_stack child_depth right_logical right_physical
      left_dense right right_nonempty right_physical_not_full =>
    exact (right.ne_nil_of_logical_pos right_nonempty rfl).elim

/-- A normalized stack occupying all of its root capacity consists of one
    dense root entry. -/
theorem BuilderNormalizedStack.full_physical_singleton {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat} {stack : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth stack root_depth
      logical_len physical_len)
    (hlogical : 0 < logical_len)
    (hphysical : physical_len = subtreeCapacity packing_factor root_depth) :
    ∃ entry, stack = [entry] ∧
      DenseTree packing_factor (maybeArcedTree entry) root_depth logical_len := by
  cases h with
  | empty => omega
  | single entry depth len base_le_depth dense nonempty =>
    exact ⟨entry, rfl, dense⟩
  | @left stack child_depth child_logical child_physical child physical_fits =>
    rw [subtreeCapacity_succ] at hphysical
    have hpos := hlayout.subtreeCapacity_pos child_depth
    omega
  | @right left right_stack child_depth right_logical right_physical
      left_dense right right_nonempty right_physical_not_full =>
    rw [subtreeCapacity_succ] at hphysical
    omega

/-- Below full capacity, the final normalized entry is a dense subtree and
    all entries before it form an aligned full-prefix stack at the next
    depth. This is the structural decomposition consumed by `finish_tree`. -/
theorem BuilderNormalizedStack.split_last_of_not_full {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat} {stack : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth stack root_depth
      logical_len physical_len)
    (hlogical : 0 < logical_len)
    (hphysical : physical_len < subtreeCapacity packing_factor root_depth) :
    ∃ prefix_stack top top_depth prefix_len top_len,
      stack = prefix_stack ++ [top] ∧
      base_depth ≤ top_depth ∧ top_depth < root_depth ∧
      DenseTree packing_factor (maybeArcedTree top) top_depth top_len ∧
      0 < top_len ∧
      BuilderStack packing_factor (top_depth + 1) prefix_stack root_depth
        prefix_len ∧
      prefix_len % subtreeCapacity packing_factor (top_depth + 1) = 0 ∧
      logical_len = prefix_len + top_len ∧
      physical_len = prefix_len + subtreeCapacity packing_factor top_depth := by
  induction h with
  | empty => omega
  | single entry depth len base_le_depth dense nonempty =>
    omega
  | @left child_stack child_depth child_logical child_physical child
      physical_fits ih =>
    by_cases hchild_full :
        child_physical = subtreeCapacity packing_factor child_depth
    · obtain ⟨entry, hentry, hdense⟩ :=
        child.full_physical_singleton hlayout hlogical hchild_full
      subst child_stack
      refine ⟨[], entry, child_depth, 0, child_logical, rfl,
        child.base_le_depth, by omega, hdense, hlogical, ?_, by simp,
        by simp, ?_⟩
      · exact BuilderStack.empty (child_depth + 1) (Nat.le_refl _)
      · simpa [hchild_full]
    · have hchild_lt : child_physical <
          subtreeCapacity packing_factor child_depth := by omega
      obtain ⟨prefix_stack, top, top_depth, prefix_len, top_len, hstack,
          hbase_depth, htop_depth, htop, htop_nonempty, hprefix, haligned,
          hlogical_len, hphysical_len⟩ := ih hlogical hchild_lt
      refine ⟨prefix_stack, top, top_depth, prefix_len, top_len, hstack,
        hbase_depth, by omega, htop, htop_nonempty,
        BuilderStack.left hprefix hprefix.length_le_capacity, haligned,
        hlogical_len, hphysical_len⟩
  | @right left right_stack child_depth right_logical right_physical left_dense
      right right_nonempty right_physical_not_full ih =>
    obtain ⟨right_prefix, top, top_depth, right_prefix_len, top_len,
        hright_stack, hbase_depth, htop_depth, htop, htop_nonempty,
        hright_prefix, hright_aligned, hright_logical, hright_physical⟩ :=
      ih right_nonempty right_physical_not_full
    have hnext_le_child : top_depth + 1 ≤ child_depth := by omega
    have hnext_dvd_child :
        subtreeCapacity packing_factor (top_depth + 1) ∣
          subtreeCapacity packing_factor child_depth := by
      rw [subtreeCapacity_eq_mul_pow_of_le packing_factor hnext_le_child]
      exact dvd_mul_right _ _
    have hchild_aligned : subtreeCapacity packing_factor child_depth %
        subtreeCapacity packing_factor (top_depth + 1) = 0 :=
      Nat.mod_eq_zero_of_dvd hnext_dvd_child
    let prefix_stack := left :: right_prefix
    have hprefix : BuilderStack packing_factor (top_depth + 1) prefix_stack
        (child_depth + 1)
        (subtreeCapacity packing_factor child_depth + right_prefix_len) := by
      by_cases hright_zero : right_prefix_len = 0
      · subst right_prefix_len
        have hright_nil := hright_prefix.eq_nil_of_length_zero_early rfl
        subst right_prefix
        have hleft := BuilderStack.full
          (packing_factor := packing_factor) (base_depth := top_depth + 1)
          left child_depth hnext_le_child left_dense
          (hlayout.subtreeCapacity_pos child_depth)
        exact BuilderStack.left hleft hleft.length_le_capacity
      · have hright_pos : 0 < right_prefix_len := Nat.pos_of_ne_zero
          hright_zero
        have hright_lt : right_prefix_len <
            subtreeCapacity packing_factor child_depth := by omega
        exact BuilderStack.right left child_depth right_prefix_len left_dense
          hright_prefix hright_pos hright_lt
    refine ⟨prefix_stack, top, top_depth,
      subtreeCapacity packing_factor child_depth + right_prefix_len, top_len,
      ?_, hbase_depth, by omega, htop, htop_nonempty, hprefix, ?_, ?_, ?_⟩
    · simp [prefix_stack, hright_stack]
    · simp [Nat.add_mod, hchild_aligned, hright_aligned]
    · omega
    · omega

theorem BuilderNormalizedStack.raise_left {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))}
    {depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor base_depth stack depth
      logical_len physical_len) (extra : Nat) :
    BuilderNormalizedStack packing_factor base_depth stack (depth + extra)
      logical_len physical_len := by
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
    rw [Nat.add_succ]
    exact BuilderNormalizedStack.left ih ih.physical_le_capacity

theorem BuilderNormalizedStack.lower_base {T : Type}
    {packing_factor : Option Std.Usize} {old_base new_base : Nat}
    {stack : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (h : BuilderNormalizedStack packing_factor old_base stack root_depth
      logical_len physical_len) (hbase : new_base ≤ old_base) :
    BuilderNormalizedStack packing_factor new_base stack root_depth logical_len
      physical_len := by
  induction h with
  | empty depth old_le_depth =>
    exact BuilderNormalizedStack.empty depth (hbase.trans old_le_depth)
  | single entry depth len old_le_depth dense nonempty =>
    exact BuilderNormalizedStack.single entry depth len
      (hbase.trans old_le_depth) dense nonempty
  | left child physical_fits ih =>
    exact BuilderNormalizedStack.left ih physical_fits
  | right left depth right_logical right_physical left_dense right
      right_nonempty right_physical_not_full ih =>
    exact BuilderNormalizedStack.right left depth right_logical right_physical
      left_dense ih right_nonempty right_physical_not_full

/-- An aligned canonical logical stack is already carry-normalized, with
    physical and logical cursors equal. -/
theorem BuilderStack.normalized_of_aligned {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {root_depth total : Nat}
    (hstack : BuilderStack packing_factor base_depth stack root_depth total)
    (haligned : total % subtreeCapacity packing_factor base_depth = 0) :
    BuilderNormalizedStack packing_factor base_depth stack root_depth total
      total := by
  have hbase_pos := hlayout.subtreeCapacity_pos base_depth
  induction hstack with
  | empty depth base_le_depth =>
    exact BuilderNormalizedStack.empty depth base_le_depth
  | base entry len dense nonempty =>
    have hfit := dense.length_le_capacity
    have hdvd := Nat.dvd_of_mod_eq_zero haligned
    have hbase_le : subtreeCapacity packing_factor base_depth ≤ len :=
      Nat.le_of_dvd nonempty hdvd
    have hlen : len = subtreeCapacity packing_factor base_depth := by omega
    simpa [hlen] using BuilderNormalizedStack.single
      (packing_factor := packing_factor) (base_depth := base_depth) entry
      base_depth len (Nat.le_refl _) dense nonempty
  | full entry depth base_le_depth dense capacity_nonempty =>
    exact BuilderNormalizedStack.single entry depth
      (subtreeCapacity packing_factor depth) base_le_depth dense
      capacity_nonempty
  | segment entry depth len base_le_depth dense nonempty
      full_or_final_partial =>
    rcases full_or_final_partial with hfull | hpartial
    · simpa [hfull] using BuilderNormalizedStack.single
        (packing_factor := packing_factor) (base_depth := base_depth) entry
        depth len base_le_depth dense nonempty
    · exact (hpartial.2 haligned).elim
  | @left child_stack child_depth child_len child_prefix child_fits ih =>
    exact BuilderNormalizedStack.left (ih haligned) child_fits
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
    have hright_aligned : right_len %
        subtreeCapacity packing_factor base_depth = 0 :=
      Nat.mod_eq_zero_of_dvd hright_dvd
    exact BuilderNormalizedStack.right left child_depth right_len right_len
      left_dense (ih hright_aligned) right_nonempty right_not_full

theorem BuilderStack.normalized_cursor_of_aligned {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {root_depth total : Nat}
    (hstack : BuilderStack packing_factor base_depth stack root_depth total)
    (haligned : total % subtreeCapacity packing_factor base_depth = 0) :
    ∃ physical_len,
      BuilderNormalizedStack packing_factor base_depth stack root_depth total
          physical_len ∧
        physical_len % subtreeCapacity packing_factor base_depth = 0 ∧
        total ≤ physical_len ∧
        physical_len < total + subtreeCapacity packing_factor base_depth := by
  exact ⟨total, hstack.normalized_of_aligned hlayout haligned, haligned,
    Nat.le_refl _, by have := hlayout.subtreeCapacity_pos base_depth; omega⟩

theorem BuilderNormalizedStack.rewrap {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack replacement : List (utils.MaybeArced (Tree T))}
    {root_depth logical_len physical_len : Nat}
    (hstack : BuilderNormalizedStack packing_factor base_depth stack root_depth
      logical_len physical_len)
    (hsame : stack.map maybeArcedTree = replacement.map maybeArcedTree) :
    BuilderNormalizedStack packing_factor base_depth replacement root_depth
      logical_len physical_len := by
  induction hstack generalizing replacement with
  | empty depth base_le_depth =>
    have hreplacement : replacement = [] := by simpa using hsame.symm
    subst replacement
    exact BuilderNormalizedStack.empty depth base_le_depth
  | single entry depth len base_le_depth dense nonempty =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement tail =>
      have hparts : maybeArcedTree entry = maybeArcedTree replacement ∧
          tail = [] := by simpa using hsame
      obtain ⟨htree, rfl⟩ := hparts
      exact BuilderNormalizedStack.single replacement depth len base_le_depth
        (by simpa [← htree] using dense) nonempty
  | left child physical_fits ih =>
    exact BuilderNormalizedStack.left (ih hsame) physical_fits
  | @right left right_stack depth right_logical right_physical left_dense
      right right_nonempty right_physical_not_full ih =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement replacement_tail =>
      have hparts : maybeArcedTree left = maybeArcedTree replacement ∧
          right_stack.map maybeArcedTree =
            replacement_tail.map maybeArcedTree := by simpa using hsame
      obtain ⟨hleft, htail⟩ := hparts
      exact BuilderNormalizedStack.right replacement depth right_logical
        right_physical (by simpa [← hleft] using left_dense) (ih htail)
        right_nonempty right_physical_not_full

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
  | segment entry depth len base_le_depth dense nonempty full_or_final_partial =>
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
  | segment entry depth len base_le_depth dense nonempty full_or_final_partial =>
    omega
  | left child_prefix fits_left ih => exact ih hzero
  | right left depth right_len left_dense right_prefix
      right_nonempty right_not_full ih => omega

theorem BuilderStack.length_eq_zero_of_nil {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {depth len : Nat}
    (h : BuilderStack packing_factor base_depth stack depth len)
    (hempty : stack = []) : len = 0 := by
  induction h with
  | empty => rfl
  | base => simp at hempty
  | full => simp at hempty
  | segment => simp at hempty
  | left child_prefix fits_left ih => exact ih hempty
  | right => simp at hempty

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

/-- Every physical stack entry represents a dense subtree; its depth and
    logical length are recovered existentially from the stack shape. -/
theorem BuilderStack.entry_dense {T : Type}
    {packing_factor : Option Std.Usize} {base_depth : Nat}
    {stack : List (utils.MaybeArced (Tree T))} {root_depth total : Nat}
    (hstack : BuilderStack packing_factor base_depth stack root_depth total)
    {entry : utils.MaybeArced (Tree T)} (hentry : entry ∈ stack) :
    ∃ depth len,
      DenseTree packing_factor (maybeArcedTree entry) depth len := by
  induction hstack with
  | empty => simp at hentry
  | base only_entry len dense nonempty =>
    simp at hentry
    subst entry
    exact ⟨base_depth, len, dense⟩
  | full only_entry depth base_le_depth dense capacity_nonempty =>
    simp at hentry
    subst entry
    exact ⟨depth, subtreeCapacity packing_factor depth, dense⟩
  | segment only_entry depth len base_le_depth dense nonempty
      full_or_final_partial =>
    simp at hentry
    subst entry
    exact ⟨depth, len, dense⟩
  | left child_prefix fits_left ih => exact ih hentry
  | right left depth right_len left_dense right_prefix right_nonempty
      right_not_full ih =>
    simp at hentry
    rcases hentry with rfl | hright
    · exact ⟨depth, subtreeCapacity packing_factor depth, left_dense⟩
    · exact ih hright

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
  | segment entry depth len base_le_depth dense nonempty full_or_final_partial =>
    cases replacement with
    | nil => simp at hsame
    | cons replacement tail =>
      have hparts : maybeArcedTree entry = maybeArcedTree replacement ∧
          tail = [] := by
        simpa using hsame
      obtain ⟨htree, rfl⟩ := hparts
      exact BuilderStack.segment replacement depth len base_le_depth
        (by simpa [← htree] using dense) nonempty full_or_final_partial
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
  stack_normalized :
    (self.level.val ≠ 0 ∨
      self.length.val % subtreeCapacity self.packing_factor
        (if self.level.val = 0 then 0
          else self.level.val - self.packing_depth.val) = 0) →
      ∃ physical_len,
        BuilderNormalizedStack self.packing_factor
            (if self.level.val = 0 then 0
              else self.level.val - self.packing_depth.val)
            self.stack.val self.depth.val self.length.val physical_len ∧
          physical_len % subtreeCapacity self.packing_factor
            (if self.level.val = 0 then 0
              else self.level.val - self.packing_depth.val) = 0 ∧
          self.length.val ≤ physical_len ∧
          physical_len < self.length.val +
            subtreeCapacity self.packing_factor
              (if self.level.val = 0 then 0
                else self.level.val - self.packing_depth.val)
  partial_leaf :
    self.level.val = 0 →
      self.length.val % subtreeCapacity self.packing_factor 0 ≠ 0 →
      ∃ prefix_stack top top_len,
        self.stack.val = prefix_stack ++
            [utils.MaybeArced.Unarced top] ∧
          DenseTree self.packing_factor top 0 top_len ∧
          0 < top_len ∧
          top_len < subtreeCapacity self.packing_factor 0

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

theorem BuilderInvariant.depth_packing_lt_bits {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    (h : BuilderInvariant ValueInst self) :
    self.depth.val + self.packing_depth.val < System.Platform.numBits := by
  have hcapacity := BuilderInvariant.builder_capacity_matches h
  rw [(BuilderInvariant.layout h).subtreeCapacity_eq_two_pow] at hcapacity
  have hbound : self.capacity.val < 2 ^ System.Platform.numBits := by
    simpa using self.capacity.hBounds
  rw [hcapacity] at hbound
  by_contra hnot_lt
  have hpow_le : 2 ^ System.Platform.numBits ≤
      2 ^ (self.packing_depth.val + self.depth.val) :=
    Nat.pow_le_pow_right (by omega) (by omega)
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

private theorem usize_shift_left_value {value shift shifted : Std.Usize}
    {unbounded : Nat}
    (h : value <<< shift = ok shifted)
    (hunbounded : unbounded = value.val * 2 ^ shift.val)
    (hfit : unbounded < 2 ^ System.Platform.numBits) :
    shifted.val = unbounded := by
  have hbound : shift.val < System.Platform.numBits := by
    change UScalar.shiftLeft value shift.val = ok shifted at h
    unfold UScalar.shiftLeft at h
    split at h
    · assumption
    · simp at h
  have hspec := UScalar.ShiftLeft_spec value shift
    (UScalar.size UScalarTy.Usize) hbound rfl
  rw [h] at hspec
  obtain ⟨hvalue, -⟩ := hspec
  rw [hvalue, Nat.shiftLeft_eq, UScalar.size_def]
  rw [hunbounded]
  apply Nat.mod_eq_of_lt
  simpa [hunbounded] using hfit

private theorem usize_add_value {left right sum : Std.Usize}
    (h : left + right = ok sum) : sum.val = left.val + right.val := by
  have hadd := UScalar.add_equiv left right
  rw [h] at hadd
  exact hadd.2.1

private theorem usize_saturating_add_value (left right : Std.Usize)
    (hfit : left.val + right.val ≤ Usize.max) :
    (core.num.Usize.saturating_add left right).val =
      left.val + right.val := by
  unfold core.num.Usize.saturating_add UScalar.saturating_add
  unfold UScalar.val
  have hfit' : left.bv.toNat + right.bv.toNat ≤
      UScalar.max UScalarTy.Usize := by
    rw [UScalar.max_USize_eq]
    exact hfit
  rw [min_eq_right hfit', BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have hmax_lt : Usize.max < 2 ^ System.Platform.numBits := by
    native_decide
  have hmax_lt' : UScalar.max UScalarTy.Usize <
      2 ^ UScalarTy.Usize.numBits := by
    rw [UScalar.max_USize_eq]
    exact hmax_lt
  exact hfit'.trans_lt hmax_lt'

private theorem usize_saturating_sub_value (left right : Std.Usize) :
    (core.num.Usize.saturating_sub left right).val =
      left.val - right.val := by
  unfold core.num.Usize.saturating_sub UScalar.saturating_sub
  unfold UScalar.val
  rw [max_eq_right (Nat.zero_le _), BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact (Nat.sub_le left.val right.val).trans_lt left.hBounds

private theorem usize_cast_u32_value (value : Std.Usize)
    (hfit : value.val < 2 ^ 32) :
    (UScalar.cast .U32 value).val = value.val := by
  rw [UScalar.cast_val_eq]
  change value.val % 2 ^ 32 = value.val
  exact Nat.mod_eq_of_lt hfit

private theorem usize_pow_two_value {exponent : Std.U32}
    {result : Std.Usize}
    (h : core.num.Usize.pow 2#usize exponent = ok result) :
    result.val = 2 ^ exponent.val := by
  unfold core.num.Usize.pow at h
  have hspec := UScalar.tryMk_eq UScalarTy.Usize
    ((2#usize).val ^ exponent.val)
  rw [h] at hspec
  simpa using hspec.1

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

private theorem usize_div_ceil_value {value divisor quotient : Std.Usize}
    (hdivisor : 0 < divisor.val)
    (hdiv : core.num.Usize.div_ceil value divisor = ok quotient) :
    quotient.val = value.val / divisor.val +
      if value.val % divisor.val = 0 then 0 else 1 := by
  unfold core.num.Usize.div_ceil at hdiv
  rw [if_neg (Nat.ne_of_gt hdivisor)] at hdiv
  have hspec := UScalar.tryMk_eq .Usize
    (value.val / divisor.val +
      if value.val % divisor.val = 0 then 0 else 1)
  rw [hdiv] at hspec
  exact hspec.1

private theorem nat_div_ceil_bounds {value divisor quotient : Nat}
    (hdivisor : 0 < divisor)
    (hquotient : quotient = value / divisor +
      if value % divisor = 0 then 0 else 1) :
    value ≤ quotient * divisor ∧
      quotient * divisor < value + divisor := by
  have hmod_lt := Nat.mod_lt value hdivisor
  have hdecomp := Nat.mod_add_div value divisor
  by_cases haligned : value % divisor = 0
  · simp [haligned] at hquotient
    constructor <;> rw [hquotient]
    · simpa [haligned, Nat.mul_comm] using hdecomp.symm.le
    · have hvalue_eq : value / divisor * divisor = value := by
        simpa [haligned, Nat.mul_comm] using hdecomp
      calc
        value / divisor * divisor < value / divisor * divisor + divisor :=
          Nat.lt_add_of_pos_right hdivisor
        _ = value + divisor := by rw [hvalue_eq]
  · simp [haligned] at hquotient
    have hmod_pos : 0 < value % divisor := Nat.pos_of_ne_zero haligned
    rw [hquotient]
    constructor
    · rw [Nat.add_mul, one_mul]
      have hbase : value = value / divisor * divisor +
          value % divisor := by
        simpa [Nat.add_comm, Nat.mul_comm] using hdecomp.symm
      omega
    · rw [Nat.add_mul, one_mul]
      have hbase : value = value / divisor * divisor +
          value % divisor := by
        simpa [Nat.add_comm, Nat.mul_comm] using hdecomp.symm
      omega

private theorem aligned_window_unique {unit start first second : Nat}
    (hunit : 0 < unit)
    (hfirst_aligned : first % unit = 0)
    (hsecond_aligned : second % unit = 0)
    (hfirst_lower : start ≤ first) (hfirst_upper : first < start + unit)
    (hsecond_lower : start ≤ second)
    (hsecond_upper : second < start + unit) : first = second := by
  obtain ⟨first_units, hfirst⟩ :=
    Nat.dvd_of_mod_eq_zero hfirst_aligned
  obtain ⟨second_units, hsecond⟩ :=
    Nat.dvd_of_mod_eq_zero hsecond_aligned
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hunits : first_units < second_units := by
      apply (Nat.mul_lt_mul_left hunit).mp
      simpa [hfirst, hsecond, Nat.mul_comm] using hlt
    have hgap : first + unit ≤ second := by
      rw [hfirst, hsecond]
      simpa [Nat.mul_add, Nat.mul_comm] using
        Nat.mul_le_mul_left unit (Nat.succ_le_iff.mpr hunits)
    omega
  · have hunits : second_units < first_units := by
      apply (Nat.mul_lt_mul_left hunit).mp
      simpa [hfirst, hsecond, Nat.mul_comm] using hgt
    have hgap : second + unit ≤ first := by
      rw [hfirst, hsecond]
      simpa [Nat.mul_add, Nat.mul_comm] using
        Nat.mul_le_mul_left unit (Nat.succ_le_iff.mpr hunits)
    omega

private theorem BuilderInvariant.finish_cursor_normalized {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    (hinvariant : BuilderInvariant ValueInst self)
    {level_capacity next_index : Std.Usize}
    (hlevel_capacity : 1#usize <<< self.level = ok level_capacity)
    (hnext_index : core.num.Usize.div_ceil self.length level_capacity =
      ok next_index)
    (hready : self.level.val ≠ 0 ∨
      self.length.val % subtreeCapacity self.packing_factor
        (if self.level.val = 0 then 0
          else self.level.val - self.packing_depth.val) = 0) :
    ∃ physical_len,
      BuilderNormalizedStack self.packing_factor
          (if self.level.val = 0 then 0
            else self.level.val - self.packing_depth.val)
          self.stack.val self.depth.val self.length.val physical_len ∧
        physical_len = next_index.val * 2 ^ self.level.val := by
  obtain ⟨physical_len, hnormalized, hphysical_aligned, hphysical_lower,
      hphysical_upper⟩ :=
    (@BuilderInvariant.stack_normalized T ValueInst self hinvariant) hready
  have hlevel_capacity_value :=
    usize_shift_left_one_value hlevel_capacity
  have hquotient := usize_div_ceil_value
    (by rw [hlevel_capacity_value]; positivity) hnext_index
  rw [hlevel_capacity_value] at hquotient
  have hrounded := nat_div_ceil_bounds
    (Nat.two_pow_pos self.level.val) hquotient
  by_cases hlevel : self.level.val = 0
  · have hlength_aligned : self.length.val %
        subtreeCapacity self.packing_factor 0 = 0 := by
      simpa [hlevel] using hready.resolve_left (not_not.mpr hlevel)
    have hcapacity_pos :=
      (BuilderInvariant.layout hinvariant).subtreeCapacity_pos 0
    have hphysical_eq : physical_len = self.length.val := by
      apply aligned_window_unique hcapacity_pos
      · simpa [hlevel] using hphysical_aligned
      · exact hlength_aligned
      · exact hphysical_lower
      · simpa [hlevel] using hphysical_upper
      · exact Nat.le_refl _
      · omega
    have hnext_eq : next_index.val = self.length.val := by
      simpa [hlevel, Nat.mod_one] using hquotient
    exact ⟨physical_len, hnormalized, by simp [hphysical_eq, hnext_eq,
      hlevel]⟩
  · have hbase_capacity := hinvariant.base_capacity_eq_pow_level
      (Or.inl hlevel)
    have hbase_capacity' : subtreeCapacity self.packing_factor
        (self.level.val - self.packing_depth.val) =
          2 ^ self.level.val := by
      simpa [hlevel] using hbase_capacity
    have hphysical_aligned' : physical_len % 2 ^ self.level.val = 0 := by
      simpa [hlevel, hbase_capacity'] using hphysical_aligned
    have hphysical_upper' : physical_len <
        self.length.val + 2 ^ self.level.val := by
      simpa [hlevel, hbase_capacity'] using hphysical_upper
    have hrounded_aligned :
        (next_index.val * 2 ^ self.level.val) % 2 ^ self.level.val = 0 := by
      simp
    have hphysical_eq : physical_len =
        next_index.val * 2 ^ self.level.val := by
      exact aligned_window_unique (Nat.two_pow_pos self.level.val)
        hphysical_aligned' hrounded_aligned hphysical_lower
        hphysical_upper' hrounded.1 hrounded.2
    exact ⟨physical_len, hnormalized, hphysical_eq⟩

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
              hlevel_bound, ?_, ?_, ?_, ?_⟩
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
            · intro _
              let base_depth :=
                if level.val = 0 then 0 else level.val - (0#usize).val
              have hbase_le : base_depth ≤ depth.val := by
                dsimp [base_depth]
                split <;> omega
              have hnormalized := BuilderNormalizedStack.empty
                (T := T) (packing_factor := none) depth.val hbase_le
              refine ⟨0, hnormalized, by simp, by simp, ?_⟩
              have hpos := PackingLayout.subtreeCapacity_pos
                (PackingLayout.unpacked factor_eq depth_eq) base_depth
              simpa [base_depth] using hpos
            · intro _ hpartial
              simp at hpartial
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
              depth_eq factor_is_power, hlevel, hlevel_bound, ?_, ?_, ?_, ?_⟩
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
            · intro _
              let base_depth := if level.val = 0 then 0 else
                level.val - packing_depth.val
              have hbase_le : base_depth ≤ depth.val := by
                dsimp [base_depth]
                split <;> omega
              have hnormalized := BuilderNormalizedStack.empty
                (T := T) (packing_factor := some factor) depth.val hbase_le
              refine ⟨0, hnormalized, by simp, by simp, ?_⟩
              have hpos := PackingLayout.subtreeCapacity_pos
                (PackingLayout.packed factor packing_depth factor_eq depth_eq
                  factor_is_power) base_depth
              simpa [base_depth] using hpos
            · intro _ hpartial
              simp at hpartial

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

theorem BuilderCarryCount.count_le_depth_sub
    {packing_factor : Option Std.Usize} {base_depth root_depth total count : Nat}
    (hcarry : BuilderCarryCount packing_factor base_depth root_depth total
      count) : count ≤ root_depth - base_depth := by
  induction hcarry with
  | zero => simp
  | inside child_depth total count child_count not_at_right ih => omega
  | enter_right => simp
  | first_merge => simp
  | right_open child_depth right_len count right_count cursor_open ih => omega
  | right_close child_depth right_len count right_count cursor_closes ih =>
    have hbase := right_count.base_le_depth
    omega

private theorem nat_bits_of_padic_succ : ∀ count value : Nat,
    count = padicValNat 2 (value + 1) →
      ((value >>> count) &&& 1) = 0 ∧
      ∀ offset, offset < count → ((value >>> offset) &&& 1) = 1 := by
  intro count
  induction count with
  | zero =>
    intro value hcount
    have hnot_dvd : ¬2 ∣ value + 1 := by
      intro hdvd
      have hnonzero : value + 1 ≠ 0 := by omega
      have hval_ne : padicValNat 2 (value + 1) ≠ 0 :=
        (dvd_iff_padicValNat_ne_zero (p := 2) hnonzero).mp hdvd
      omega
    have hodd_ne : (value + 1) % 2 ≠ 0 := by
      exact fun hmod => hnot_dvd (Nat.dvd_of_mod_eq_zero hmod)
    have hvalue_even : value % 2 = 0 := by omega
    constructor
    · simpa [Nat.and_one_is_mod] using hvalue_even
    · intro offset hoff
      omega
  | succ count ih =>
    intro value hcount
    have hnonzero : value + 1 ≠ 0 := by omega
    have hdvd : 2 ∣ value + 1 := by
      apply (dvd_iff_padicValNat_ne_zero (p := 2) hnonzero).mpr
      omega
    have hsum_even : (value + 1) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    have hvalue_odd : value % 2 = 1 := by omega
    let half := value / 2
    have hvalue : value = 2 * half + 1 := by
      have hdivision := Nat.mod_add_div value 2
      dsimp [half]
      omega
    have hhalf : (value + 1) / 2 = half + 1 := by
      rw [hvalue]
      omega
    have hdiv_val := padicValNat.div (p := 2) hdvd
    have hhalf_count : count = padicValNat 2 (half + 1) := by
      rw [hhalf] at hdiv_val
      omega
    obtain ⟨hstop, hmerge⟩ := ih half hhalf_count
    have hshift_one : (2 * half + 1) >>> 1 = half := by
      rw [Nat.shiftRight_one]
      omega
    constructor
    · rw [hvalue]
      rw [Nat.add_comm count 1, Nat.shiftRight_add]
      rw [hshift_one]
      exact hstop
    · intro offset hoff
      cases offset with
      | zero => simpa [Nat.and_one_is_mod] using hvalue_odd
      | succ offset =>
        rw [hvalue]
        rw [Nat.add_comm offset 1, Nat.shiftRight_add]
        rw [hshift_one]
        exact hmerge offset (by omega)

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

/-- The bit schedule consumed by the translated finish merge loop. -/
structure BuilderMergeBits (cursor start count root_depth packing_depth : Nat) :
    Prop where
  merge : ∀ offset, offset < count →
    start + offset < root_depth ∧
      ((cursor >>> (start + offset + packing_depth)) &&& 1) = 1
  stop : start + count ≥ root_depth ∨
    ((cursor >>> (start + count + packing_depth)) &&& 1) = 0

private theorem finish_cursor_shift {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {top_depth total physical units offset : Nat}
    (htotal : total =
      subtreeCapacity packing_factor (top_depth + 1) * units)
    (hphysical : physical =
      total + subtreeCapacity packing_factor top_depth) :
    physical >>> (top_depth + 1 + offset + packing_depth.val) =
      units >>> offset := by
  have htop := hlayout.subtreeCapacity_eq_two_pow top_depth
  have hparent := hlayout.subtreeCapacity_eq_two_pow (top_depth + 1)
  let exponent := top_depth + packing_depth.val
  have hphysical_value : physical = 2 ^ exponent * (2 * units + 1) := by
    rw [hphysical, htotal, htop, hparent]
    have htop_exponent : packing_depth.val + top_depth = exponent := by
      dsimp [exponent]
      omega
    have hparent_exponent : packing_depth.val + (top_depth + 1) =
        exponent + 1 := by
      dsimp [exponent]
      omega
    rw [htop_exponent, hparent_exponent, pow_succ]
    ring
  have hfirst : physical >>> exponent = 2 * units + 1 := by
    rw [hphysical_value, Nat.shiftRight_eq_div_pow]
    rw [Nat.mul_comm]
    exact Nat.mul_div_left _ (Nat.two_pow_pos exponent)
  rw [show top_depth + 1 + offset + packing_depth.val =
    exponent + (1 + offset) by omega, Nat.shiftRight_add, hfirst,
    Nat.shiftRight_add]
  have hone : (2 * units + 1) >>> 1 = units := by
    rw [Nat.shiftRight_one]
    omega
  rw [hone]

theorem BuilderCarryCount.finish_merge_bits {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {top_depth root_depth total count physical : Nat}
    (hcarry : BuilderCarryCount packing_factor (top_depth + 1) root_depth
      total count)
    (hphysical : physical =
      total + subtreeCapacity packing_factor top_depth) :
    BuilderMergeBits physical (top_depth + 1) count root_depth
      packing_depth.val := by
  obtain ⟨units, htotal, hcount⟩ := hcarry.eq_padic_units hlayout
  obtain ⟨hstop_bit, hmerge_bits⟩ :=
    nat_bits_of_padic_succ count units hcount
  refine ⟨?_, ?_⟩
  · intro offset hoffset
    have hcount_bound := hcarry.count_le_depth_sub
    constructor
    · have hbase := hcarry.base_le_depth
      omega
    · rw [finish_cursor_shift hlayout htotal hphysical]
      exact hmerge_bits offset hoffset
  · by_cases hroot : top_depth + 1 + count ≥ root_depth
    · exact Or.inl hroot
    · exact Or.inr (by
        rw [finish_cursor_shift hlayout htotal hphysical]
        exact hstop_bit)

private theorem finish_partial_cursor_shift {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {total top_len cursor units offset : Nat}
    (htotal : total = subtreeCapacity packing_factor 0 * units)
    (hcursor : cursor = total + top_len)
    (htop_partial : top_len < subtreeCapacity packing_factor 0) :
    cursor >>> (offset + packing_depth.val) = units >>> offset := by
  have hcapacity : subtreeCapacity packing_factor 0 =
      2 ^ packing_depth.val := by
    simpa using hlayout.subtreeCapacity_eq_two_pow 0
  have hbase_shift : cursor >>> packing_depth.val = units := by
    rw [Nat.shiftRight_eq_div_pow, hcursor, htotal, hcapacity,
      Nat.mul_add_div (Nat.two_pow_pos packing_depth.val),
      Nat.div_eq_of_lt (by simpa [hcapacity] using htop_partial)]
    simp
  rw [show offset + packing_depth.val = packing_depth.val + offset by omega,
    Nat.shiftRight_add, hbase_shift]

/-- When the final packed leaf is partial, its low bits do not affect the
    binary carry schedule above the packing boundary. -/
theorem BuilderCarryCount.finish_partial_merge_bits {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {root_depth total count top_len cursor : Nat}
    (hcarry : BuilderCarryCount packing_factor 0 root_depth total count)
    (hcursor : cursor = total + top_len)
    (htop_partial : top_len < subtreeCapacity packing_factor 0) :
    BuilderMergeBits cursor 0 count root_depth packing_depth.val := by
  obtain ⟨units, htotal, hcount⟩ := hcarry.eq_padic_units hlayout
  obtain ⟨hstop_bit, hmerge_bits⟩ :=
    nat_bits_of_padic_succ count units hcount
  refine ⟨?_, ?_⟩
  · intro offset hoffset
    constructor
    · have hcount_bound := hcarry.count_le_depth_sub
      omega
    · rw [show 0 + offset + packing_depth.val =
          offset + packing_depth.val by omega,
        finish_partial_cursor_shift hlayout htotal hcursor htop_partial]
      exact hmerge_bits offset hoffset
  · by_cases hroot : count ≥ root_depth
    · exact Or.inl (by omega)
    · exact Or.inr (by
        rw [show 0 + count + packing_depth.val =
            count + packing_depth.val by omega,
          finish_partial_cursor_shift hlayout htotal hcursor htop_partial]
        exact hstop_bit)

private theorem finish_top_depth_eq {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth level next_index : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {top_depth root_depth total physical units : Nat}
    (htotal : total =
      subtreeCapacity packing_factor (top_depth + 1) * units)
    (htop_lt : top_depth < root_depth)
    (hphysical : physical =
      total + subtreeCapacity packing_factor top_depth)
    (hcursor : physical = next_index.val * 2 ^ level.val)
    (hlevel : level.val ≤ top_depth + packing_depth.val)
    (hroot_bits : root_depth + packing_depth.val <
      System.Platform.numBits)
    {zeros : Std.U32}
    (hzeros : core.num.Usize.trailing_zeros next_index = ok zeros) :
    (core.num.Usize.saturating_sub
      (core.num.Usize.saturating_add (UScalar.cast .Usize zeros) level)
      packing_depth).val = top_depth := by
  have htop := hlayout.subtreeCapacity_eq_two_pow top_depth
  have hparent := hlayout.subtreeCapacity_eq_two_pow (top_depth + 1)
  let exponent := top_depth + packing_depth.val
  have hphysical_value : physical = 2 ^ exponent * (2 * units + 1) := by
    rw [hphysical, htotal, htop, hparent]
    have htop_exponent : packing_depth.val + top_depth = exponent := by
      dsimp [exponent]
      omega
    have hparent_exponent : packing_depth.val + (top_depth + 1) =
        exponent + 1 := by
      dsimp [exponent]
      omega
    rw [htop_exponent, hparent_exponent, pow_succ]
    ring
  have hphysical_val : padicValNat 2 physical = exponent := by
    rw [hphysical_value, padicValNat.mul (by positivity) (by omega),
      padicValNat.prime_pow]
    have hodd : ¬2 ∣ 2 * units + 1 := by omega
    rw [padicValNat.eq_zero_of_not_dvd hodd]
    simp
  have hnext_pos : 0 < next_index.val := by
    have hphysical_pos : 0 < physical := by
      rw [hphysical_value]
      positivity
    by_contra hnot_pos
    have hzero : next_index.val = 0 := by omega
    rw [hcursor, hzero] at hphysical_pos
    simp at hphysical_pos
  have hcursor_val : padicValNat 2 physical =
      padicValNat 2 next_index.val + level.val := by
    rw [hcursor, padicValNat.mul (by omega) (by positivity),
      padicValNat.prime_pow]
  have hzeros_value := usize_trailing_zeros_padic hnext_pos hzeros
  have hsum : zeros.val + level.val = exponent := by omega
  have hcast : (UScalar.cast .Usize zeros).val = zeros.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    exact zeros.hBounds.trans_le (by native_decide)
  have hexponent_bits : exponent < System.Platform.numBits := by
    dsimp [exponent]
    omega
  have hadd_fit : (UScalar.cast .Usize zeros).val + level.val ≤ Usize.max := by
    rw [hcast, hsum]
    have hbits_le_max : System.Platform.numBits ≤ Usize.max := by native_decide
    omega
  rw [usize_saturating_sub_value,
    usize_saturating_add_value _ _ hadd_fit, hcast, hsum]
  dsimp [exponent]
  omega

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
        BuilderNormalizedStack packing_factor base_depth
          (final_stack ++ [utils.MaybeArced.Unarced final_top]) root_depth
          (total + top_len)
          (total + subtreeCapacity packing_factor base_depth) ∧
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
    have hnormalized_base := BuilderNormalizedStack.single
      (packing_factor := packing_factor) (base_depth := base_depth)
      (utils.MaybeArced.Unarced top) base_depth top_len (Nat.le_refl _) htop
      htop_nonempty
    have hnormalized := hnormalized_base.raise_left (depth - base_depth)
    rw [hdepth] at hnormalized
    refine ⟨0, [], top, base_depth, top_len,
      BuilderMergePlan.done [] top base_depth top_len htop htop_nonempty,
      BuilderCarryCount.zero depth base_le_depth,
      by simpa using hraised, by simpa using hnormalized, ?_⟩
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
      full_or_final_partial =>
    rcases full_or_final_partial with hfull | hpartial
    · omega
    · exact (hpartial.2 haligned).elim
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
              (subtreeCapacity packing_factor (base_depth + 1) -
                    subtreeCapacity packing_factor base_depth <
                  subtreeCapacity packing_factor base_depth + top_len ∧
                (subtreeCapacity packing_factor base_depth + top_len) %
                    subtreeCapacity packing_factor base_depth ≠ 0) := by
          by_cases htop_full :
              top_len = subtreeCapacity packing_factor base_depth
          · left
            rw [htop_full, subtreeCapacity_succ]
            simp [two_mul]
          · right
            have htop_lt : top_len <
                subtreeCapacity packing_factor base_depth := by omega
            constructor
            · rw [subtreeCapacity_succ]
              omega
            · rw [Nat.add_mod, Nat.mod_self, zero_add,
                Nat.mod_eq_of_lt htop_lt]
              simpa [Nat.mod_eq_of_lt htop_lt] using
                Nat.ne_of_gt htop_nonempty
        have hcanonical := BuilderStack.segment
          (packing_factor := packing_factor) (base_depth := base_depth)
          (utils.MaybeArced.Unarced merged) (base_depth + 1)
          (subtreeCapacity packing_factor base_depth + top_len) (by omega)
          hmerged_dense (by omega) hshape
        have hnormalized := BuilderNormalizedStack.single
          (packing_factor := packing_factor) (base_depth := base_depth)
          (utils.MaybeArced.Unarced merged) (base_depth + 1)
          (subtreeCapacity packing_factor base_depth + top_len) (by omega)
          hmerged_dense (by omega)
        exact ⟨1, [], merged, base_depth + 1,
          subtreeCapacity packing_factor base_depth + top_len, by simpa using hplan,
          (by simpa [hchild_full] using
            (BuilderCarryCount.first_merge (packing_factor := packing_factor)
              (base_depth := base_depth))),
          by simpa [hchild_full] using hcanonical,
          by simpa [hchild_full, subtreeCapacity_succ, two_mul] using
            hnormalized, by
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
        have hnormalized_base := BuilderNormalizedStack.single
          (packing_factor := packing_factor) (base_depth := base_depth)
          (utils.MaybeArced.Unarced top) base_depth top_len (Nat.le_refl _) htop
          htop_nonempty
        have hnormalized_right :=
          hnormalized_base.raise_left (child_depth - base_depth)
        rw [hdepth] at hnormalized_right
        have hnormalized := BuilderNormalizedStack.right
          (base_depth := base_depth) left child_depth top_len
          (subtreeCapacity packing_factor base_depth) hleft_dense
          hnormalized_right htop_nonempty hcap_lt
        have hcanonical := BuilderStack.right (base_depth := base_depth) left
          child_depth top_len hleft_dense hright htop_nonempty htop_lt
        have hplan := BuilderMergePlan.done (ValueInst := ValueInst) [left] top
          base_depth top_len htop htop_nonempty
        exact ⟨0, [left], top, base_depth, top_len, hplan,
          (by simpa [hchild_full] using
            (BuilderCarryCount.enter_right (packing_factor := packing_factor)
              child_depth hdepth_lt)),
          by simpa [hchild_full] using hcanonical,
          by simpa [hchild_full] using hnormalized, by
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
          hplan, hcarry, hcanonical, hnormalized, hcursor⟩ :=
        ih htop htop_nonempty haligned hchild_sum htop_fit
      have hphysical_fits : child_len +
          subtreeCapacity packing_factor base_depth ≤
          subtreeCapacity packing_factor child_depth :=
        aligned_add_le hbase_pos haligned hchild_aligned hchild_lt
          (Nat.le_refl _)
      exact ⟨count, final_stack, final_top, final_depth, final_len, hplan,
        BuilderCarryCount.inside child_depth child_len count hcarry hchild_lt,
        BuilderStack.left hcanonical hcanonical.length_le_capacity,
        BuilderNormalizedStack.left hnormalized hphysical_fits, by
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
        hplan, hcarry, hright_canonical, hright_normalized, hcursor⟩ :=
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
            (subtreeCapacity packing_factor (child_depth + 1) -
                  subtreeCapacity packing_factor base_depth <
                subtreeCapacity packing_factor child_depth +
                  (right_len + top_len) ∧
              (subtreeCapacity packing_factor child_depth +
                  (right_len + top_len)) %
                  subtreeCapacity packing_factor base_depth ≠ 0) := by
        by_cases htop_full :
            top_len = subtreeCapacity packing_factor base_depth
        · left
          rw [subtreeCapacity_succ]
          simp [two_mul]
          omega
        · right
          have htop_lt : top_len <
              subtreeCapacity packing_factor base_depth := by omega
          constructor
          · rw [subtreeCapacity_succ]
            omega
          · rw [Nat.add_mod, hchild_aligned, zero_add, Nat.add_mod,
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
      have hnormalized := BuilderNormalizedStack.single
        (packing_factor := packing_factor) (base_depth := base_depth)
        (utils.MaybeArced.Unarced merged) (child_depth + 1)
        (subtreeCapacity packing_factor child_depth + (right_len + top_len))
        (by have := right_prefix.base_le_depth; omega) hmerged_dense (by omega)
      exact ⟨count + 1, [], merged, child_depth + 1,
        subtreeCapacity packing_factor child_depth + (right_len + top_len),
        hcombined, BuilderCarryCount.right_close child_depth right_len count
          hcarry hcursor_full,
        by simpa [Nat.add_assoc] using hcanonical,
        by simpa [Nat.add_assoc, hcursor_full, subtreeCapacity_succ, two_mul]
          using hnormalized, by
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
      have hnormalized := BuilderNormalizedStack.right
        (base_depth := base_depth) left child_depth (right_len + top_len)
        (right_len + subtreeCapacity packing_factor base_depth) left_dense
        hright_normalized hnew_nonempty (by omega)
      exact ⟨count, [left] ++ final_stack, final_top, final_depth, final_len,
        hplan.prepend [left], BuilderCarryCount.right_open child_depth right_len
          count hcarry (by omega),
        by simpa [Nat.add_assoc] using hcanonical,
        by simpa [Nat.add_assoc] using hnormalized, by
          intro hfilled
          rw [subtreeCapacity_succ] at hfilled
          omega⟩

/-- Replacing a normalized stack's final subtree by the same subtree padded
    on the right is an ordinary carry at the next depth. -/
theorem BuilderStack.finish_padding_plan {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {base_depth root_depth top_depth prefix_len top_len logical_len
      physical_len : Nat}
    {prefix_stack : List (utils.MaybeArced (Tree T))}
    {top : utils.MaybeArced (Tree T)} {zero padded : Tree T}
    (hprefix : BuilderStack packing_factor (top_depth + 1) prefix_stack
      root_depth prefix_len)
    (hbase : base_depth ≤ top_depth + 1)
    (haligned : prefix_len %
      subtreeCapacity packing_factor (top_depth + 1) = 0)
    (htop : DenseTree packing_factor (maybeArcedTree top) top_depth top_len)
    (htop_nonempty : 0 < top_len)
    (hzero : DenseTree packing_factor zero top_depth 0)
    (hpad : Tree.node_unboxed ValueInst (maybeArcedTree top) zero = ok padded)
    (hlogical : logical_len = prefix_len + top_len)
    (hphysical : physical_len =
      prefix_len + subtreeCapacity packing_factor top_depth)
    (hphysical_bound : physical_len ≤
      subtreeCapacity packing_factor root_depth) :
    ∃ count final_stack final_top final_depth final_len,
      BuilderMergePlan ValueInst packing_factor count prefix_stack padded
        final_stack final_top final_depth final_len ∧
      BuilderCarryCount packing_factor (top_depth + 1) root_depth prefix_len
        count ∧
      BuilderNormalizedStack packing_factor base_depth
        (final_stack ++ [utils.MaybeArced.Unarced final_top]) root_depth
        logical_len
        (physical_len + subtreeCapacity packing_factor top_depth) := by
  obtain ⟨candidate, hcandidate, hpadded⟩ :=
    node_unboxed_preserves_dense ValueInst (maybeArcedTree top) zero top_depth
      top_len 0 htop hzero htop_nonempty (by simp)
  rw [hpad] at hcandidate
  cases hcandidate
  have hlogical_fit : prefix_len + top_len ≤
      subtreeCapacity packing_factor root_depth := by
    have htop_fit := htop.length_le_capacity
    omega
  obtain ⟨count, final_stack, final_top, final_depth, final_len, hplan,
      hcarry, hcanonical, hnormalized, hcursor_full⟩ :=
    hprefix.append_subtree hlayout hpadded htop_nonempty haligned hlogical_fit
  refine ⟨count, final_stack, final_top, final_depth, final_len, hplan,
    hcarry, ?_⟩
  have hlowered := hnormalized.lower_base hbase
  have hcapacity_succ := subtreeCapacity_succ packing_factor top_depth
  rw [hcapacity_succ] at hlowered
  rw [hlogical, hphysical]
  convert hlowered using 1 <;> omega

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
      full_or_final_partial =>
    rcases full_or_final_partial with hfull | hpartial
    · omega
    · exact (hpartial.2 haligned).elim
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
      full_or_final_partial =>
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

private theorem vec_pop_some_values {A X : Type}
    (source rest : alloc.vec.Vec X) (last : X)
    (hpop : alloc.vec.Vec.pop A source = ok (some last, rest)) :
    source.val = rest.val ++ [last] := by
  unfold alloc.vec.Vec.pop at hpop
  split at hpop
  · simp at hpop
  · rename_i head tail hreverse
    simp at hpop
    obtain ⟨rfl, hrest⟩ := hpop
    have hsource : source.val = tail.reverse ++ [head] := by
      calc
        source.val = source.val.reverse.reverse := by simp
        _ = (head :: tail).reverse := by rw [hreverse]
        _ = tail.reverse ++ [head] := by simp
    have hrest_values : tail.reverse = rest.val :=
      congrArg Subtype.val hrest
    rw [hrest_values] at hsource
    exact hsource

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

private theorem finish_level_loop_step {T : Type} (ValueInst : Value T)
    (self : builder.Builder T) (next_index_on_level i : Std.Usize) :
    builder.Builder.finish_level_loop ValueInst self next_index_on_level i =
      match builder.Builder.finish_level_loop.body ValueInst
          next_index_on_level self i with
      | ok (.cont (self1, i1)) =>
        builder.Builder.finish_level_loop ValueInst self1 next_index_on_level i1
      | ok (.done result) => ok result
      | fail error => fail error
      | div => div := by
  conv_lhs => unfold builder.Builder.finish_level_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hbody : builder.Builder.finish_level_loop.body ValueInst
      next_index_on_level self i with
  | fail error => simp [hbody]
  | div => simp [hbody]
  | ok flow =>
    cases flow with
    | cont state =>
      obtain ⟨self1, i1⟩ := state
      simp [hbody]
      rfl
    | done result => simp [hbody]

private theorem finish_packed_leaf_loop_step {T : Type}
    (ValueInst : Value T) (self : builder.Builder T)
    (next_index_on_level i : Std.Usize) :
    builder.Builder.finish_packed_leaf_loop ValueInst self
        next_index_on_level i =
      match builder.Builder.finish_packed_leaf_loop.body ValueInst
          next_index_on_level self i with
      | ok (.cont (self1, i1)) =>
        builder.Builder.finish_packed_leaf_loop ValueInst self1
          next_index_on_level i1
      | ok (.done result) => ok result
      | fail error => fail error
      | div => div := by
  conv_lhs => unfold builder.Builder.finish_packed_leaf_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hbody : builder.Builder.finish_packed_leaf_loop.body ValueInst
      next_index_on_level self i with
  | fail error => simp [hbody]
  | div => simp [hbody]
  | ok flow =>
    cases flow with
    | cont state =>
      obtain ⟨self1, i1⟩ := state
      simp [hbody]
      rfl
    | done result => simp [hbody]

private theorem finish_tree_loop_step {T : Type} (ValueInst : Value T)
    (self : builder.Builder T) (next_index_on_level : Std.Usize) :
    builder.Builder.finish_tree_loop ValueInst self next_index_on_level =
      match builder.Builder.finish_tree_loop.body ValueInst self
          next_index_on_level with
      | ok (.cont (self1, next_index_on_level1)) =>
        builder.Builder.finish_tree_loop ValueInst self1 next_index_on_level1
      | ok (.done result) => ok result
      | fail error => fail error
      | div => div := by
  conv_lhs => unfold builder.Builder.finish_tree_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hbody : builder.Builder.finish_tree_loop.body ValueInst self
      next_index_on_level with
  | fail error => simp [hbody]
  | div => simp [hbody]
  | ok flow =>
    cases flow with
    | cont state =>
      obtain ⟨self1, next_index_on_level1⟩ := state
      simp [hbody]
      rfl
    | done result => simp [hbody]

private theorem finish_tree_body_done_ok_eq_capacity {T : Type}
    {ValueInst : Value T} {self result : builder.Builder T}
    {next_index : Std.Usize} {physical_len : Nat}
    (hcapacity : self.capacity.val =
      subtreeCapacity self.packing_factor self.depth.val)
    (hcursor : physical_len = next_index.val * 2 ^ self.level.val)
    (hcursor_fit : physical_len < 2 ^ System.Platform.numBits)
    (hbody : builder.Builder.finish_tree_loop.body ValueInst self next_index =
      ok (.done (core.result.Result.Ok (), result))) :
    physical_len = subtreeCapacity self.packing_factor self.depth.val ∧
      result = self := by
  unfold builder.Builder.finish_tree_loop.body at hbody
  cases hshift : next_index <<< self.level with
  | fail error => simp [hshift] at hbody
  | div => simp [hshift] at hbody
  | ok shifted_cursor =>
    simp only [hshift, bind_tc_ok] at hbody
    have hshift_value := usize_shift_left_value hshift hcursor hcursor_fit
    by_cases heq : shifted_cursor = self.capacity
    · have heq_value := congrArg UScalar.val heq
      have hstop : (shifted_cursor != self.capacity) = false := by simp [heq]
      rw [hstop] at hbody
      simp at hbody
      subst result
      exact ⟨by omega, rfl⟩
    · have hcontinue : (shifted_cursor != self.capacity) = true := by
        simp [heq]
      rw [hcontinue] at hbody
      simp only [↓reduceIte] at hbody
      cases hzeros : core.num.Usize.trailing_zeros next_index with
      | fail error => simp [hzeros] at hbody
      | div => simp [hzeros] at hbody
      | ok zeros =>
        simp only [hzeros, bind_tc_ok, lift] at hbody
        let depth := core.num.Usize.saturating_sub
          (core.num.Usize.saturating_add (UScalar.cast .Usize zeros)
            self.level) self.packing_depth
        cases hpop : alloc.vec.Vec.pop Global self.stack with
        | fail error => simp [hpop] at hbody
        | div => simp [hpop] at hbody
        | ok pop_result =>
          obtain ⟨popped, popped_stack⟩ := pop_result
          simp only [hpop, bind_tc_ok] at hbody
          cases popped with
          | none =>
            simp [core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbody
          | some top =>
            simp [core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch] at hbody
            cases hzero : Tree.zero ValueInst depth with
            | fail error =>
              dsimp [depth] at hzero
              simp [hzero] at hbody
            | div =>
              dsimp [depth] at hzero
              simp [hzero] at hbody
            | ok zero =>
              dsimp [depth] at hzero
              simp only [hzero, bind_tc_ok] at hbody
              cases hpad : Tree.node_unboxed ValueInst (maybeArcedTree top)
                  zero with
              | fail error => simp [hpad] at hbody
              | div => simp [hpad] at hbody
              | ok padded =>
                simp only [hpad, bind_tc_ok] at hbody
                cases hpush : alloc.vec.Vec.push popped_stack
                    (utils.MaybeArced.Unarced padded) with
                | fail error => simp [hpush] at hbody
                | div => simp [hpush] at hbody
                | ok padded_stack =>
                  simp only [hpush, bind_tc_ok] at hbody
                  let padded_self : builder.Builder T :=
                    { self with stack := padded_stack }
                  cases hfinish : builder.Builder.finish_level ValueInst
                      padded_self next_index depth with
                  | fail error =>
                    dsimp [padded_self, depth] at hfinish
                    simp [hfinish] at hbody
                  | div =>
                    dsimp [padded_self, depth] at hfinish
                    simp [hfinish] at hbody
                  | ok finish_result =>
                    obtain ⟨status, finished_self⟩ := finish_result
                    dsimp [padded_self, depth] at hfinish
                    simp only [hfinish, bind_tc_ok] at hbody
                    cases status with
                    | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbody
                    | Ok success =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch] at hbody
                      cases hadd : depth + finished_self.packing_depth with
                      | fail error =>
                        dsimp [depth] at hadd
                        simp [hadd] at hbody
                      | div =>
                        dsimp [depth] at hadd
                        simp [hadd] at hbody
                      | ok with_packing =>
                        dsimp [depth] at hadd
                        simp only [hadd, bind_tc_ok] at hbody
                        cases hsub : with_packing - finished_self.level with
                        | fail error => simp [hsub] at hbody
                        | div => simp [hsub] at hbody
                        | ok exponent =>
                          simp only [hsub, bind_tc_ok] at hbody
                          cases hpow : core.num.Usize.pow 2#usize
                              (UScalar.cast .U32 exponent) with
                          | fail error => simp [hpow] at hbody
                          | div => simp [hpow] at hbody
                          | ok increment =>
                            simp only [hpow, bind_tc_ok] at hbody
                            cases hnext : next_index + increment with
                            | fail error => simp [hnext] at hbody
                            | div => simp [hnext] at hbody
                            | ok next_index1 => simp [hnext] at hbody

private theorem finish_tree_body_cont_lt_capacity {T : Type}
    {ValueInst : Value T} {self next_self : builder.Builder T}
    {next_index next_index1 : Std.Usize} {physical_len : Nat}
    (hcapacity : self.capacity.val =
      subtreeCapacity self.packing_factor self.depth.val)
    (hphysical_le : physical_len ≤
      subtreeCapacity self.packing_factor self.depth.val)
    (hcursor : physical_len = next_index.val * 2 ^ self.level.val)
    (hcursor_fit : physical_len < 2 ^ System.Platform.numBits)
    (hbody : builder.Builder.finish_tree_loop.body ValueInst self next_index =
      ok (.cont (next_self, next_index1))) :
    physical_len < subtreeCapacity self.packing_factor self.depth.val := by
  unfold builder.Builder.finish_tree_loop.body at hbody
  cases hshift : next_index <<< self.level with
  | fail error => simp [hshift] at hbody
  | div => simp [hshift] at hbody
  | ok shifted_cursor =>
    simp only [hshift, bind_tc_ok] at hbody
    have hshift_value := usize_shift_left_value hshift hcursor hcursor_fit
    by_cases heq : shifted_cursor = self.capacity
    · have hstop : (shifted_cursor != self.capacity) = false := by simp [heq]
      rw [hstop] at hbody
      simp at hbody
    · have hne_value : shifted_cursor.val ≠ self.capacity.val := by
        intro heq_value
        exact heq (UScalar.eq_of_val_eq heq_value)
      rw [hshift_value, hcapacity] at hne_value
      omega

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

private theorem finish_packed_leaf_loop_follows_merge_plan {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {count cursor start root_depth packing_depth : Nat}
    {input_stack : List (utils.MaybeArced (Tree T))} {input_top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth final_len : Nat}
    (hplan : BuilderMergePlan ValueInst packing_factor count input_stack
      input_top final_stack final_top final_depth final_len)
    (hbits : BuilderMergeBits cursor start count root_depth packing_depth) :
    ∀ (self : builder.Builder T) (next_index_on_level i : Std.Usize)
      (result_stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
      (result_depth result_level : Std.Usize) (result_length : utils.Length)
      (result_factor : Option Std.Usize)
      (result_packing_depth result_capacity : Std.Usize),
      self.depth.val = root_depth →
      self.packing_depth.val = packing_depth →
      cursor = next_index_on_level.val →
      i.val = start →
      self.stack.val = input_stack ++
        [utils.MaybeArced.Unarced input_top] →
      builder.Builder.finish_packed_leaf_loop ValueInst self
          next_index_on_level i =
        ok (core.result.Result.Ok (), result_stack, result_depth, result_level,
          result_length, result_factor, result_packing_depth,
          result_capacity) →
      result_stack.val = final_stack ++
          [utils.MaybeArced.Unarced final_top] ∧
        result_depth = self.depth ∧ result_level = self.level ∧
        result_length = self.length ∧ result_factor = self.packing_factor ∧
        result_packing_depth = self.packing_depth ∧
        result_capacity = self.capacity := by
  induction hplan generalizing start with
  | done plan_stack top depth len top_dense top_nonempty =>
    intro self next_index i result_stack result_depth result_level result_length
      result_factor result_packing_depth result_capacity hdepth hpacking_depth
      hcursor hi hstack hloop
    rw [finish_packed_leaf_loop_step] at hloop
    unfold builder.Builder.finish_packed_leaf_loop.body at hloop
    by_cases hlt : i < self.depth
    · simp only [hlt, ↓reduceIte, bind_tc_ok] at hloop
      cases hadd : i + self.packing_depth with
      | fail error => simp [hadd] at hloop
      | div => simp [hadd] at hloop
      | ok shift =>
        simp only [hadd, bind_tc_ok] at hloop
        cases hright : next_index >>> shift with
        | fail error => simp [hright] at hloop
        | div => simp [hright] at hloop
        | ok shifted =>
          have hshift_value := usize_add_value hadd
          have hshifted_value := usize_shift_right_value hright
          have hmerge_stop := hbits.stop
          have hlt_value : start < root_depth := by scalar_tac
          have hstop_nat :
              ((cursor >>> (start + packing_depth)) &&& 1) = 0 := by
            rcases hmerge_stop with hroot | hbit
            · omega
            · simpa using hbit
          have hbit : (shifted &&& 1#usize) = 0#usize := by
            apply UScalar.eq_of_val_eq
            simpa [hshifted_value, hshift_value, hcursor, hi,
              hpacking_depth] using hstop_nat
          simp [hright, hbit] at hloop
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hloop
          exact ⟨hstack, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [hlt] at hloop
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hloop
      exact ⟨hstack, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | @step base_stack left top merged depth top_len remaining_count final_stack
      final_top final_depth final_len left_dense top_dense top_nonempty merge_eq
      remaining ih =>
    intro self next_index i result_stack result_depth result_level result_length
      result_factor result_packing_depth result_capacity hdepth hpacking_depth
      hcursor hi hstack hloop
    have hmerge_zero := hbits.merge 0 (by omega)
    have hlt : i < self.depth := by scalar_tac
    rw [finish_packed_leaf_loop_step] at hloop
    unfold builder.Builder.finish_packed_leaf_loop.body at hloop
    simp only [hlt, ↓reduceIte, bind_tc_ok] at hloop
    cases hadd_shift : i + self.packing_depth with
    | fail error => simp [hadd_shift] at hloop
    | div => simp [hadd_shift] at hloop
    | ok shift =>
      simp only [hadd_shift, bind_tc_ok] at hloop
      cases hright_shift : next_index >>> shift with
      | fail error => simp [hright_shift] at hloop
      | div => simp [hright_shift] at hloop
      | ok shifted =>
        have hshift_value := usize_add_value hadd_shift
        have hshifted_value := usize_shift_right_value hright_shift
        have hbit : (shifted &&& 1#usize) = 1#usize := by
          apply UScalar.eq_of_val_eq
          simpa [hshifted_value, hshift_value, hcursor, hi,
            hpacking_depth] using hmerge_zero.2
        have hsource_values : self.stack.val =
            (base_stack ++ [left]) ++
              [utils.MaybeArced.Unarced top] := hstack
        obtain ⟨after_top, hpop_top, hafter_top⟩ :=
          vec_pop_append_last (A := Global) self.stack
            (base_stack ++ [left]) (utils.MaybeArced.Unarced top)
            hsource_values
        obtain ⟨after_left, hpop_left, hafter_left⟩ :=
          vec_pop_append_last (A := Global) after_top base_stack left
            hafter_top
        simp [hright_shift, hbit, lift, hpop_top, hpop_left,
          core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          maybeArced_arced, merge_eq] at hloop
        cases hpush : alloc.vec.Vec.push after_left
            (utils.MaybeArced.Unarced merged) with
        | fail error => simp [hpush] at hloop
        | div => simp [hpush] at hloop
        | ok pushed =>
          simp only [hpush, bind_tc_ok] at hloop
          cases hnext : i + 1#usize with
          | fail error => simp [hnext] at hloop
          | div => simp [hnext] at hloop
          | ok next_i =>
            simp only [hnext, bind_tc_ok] at hloop
            have hpushed := vec_push_values after_left
              (utils.MaybeArced.Unarced merged) hpush
            have hpushed_values : pushed.val =
                base_stack ++ [utils.MaybeArced.Unarced merged] := by
              simpa [hafter_left] using hpushed
            have hnext_value := usize_add_one_value hnext
            have hi_next : next_i.val = start + 1 := by omega
            let next_self := { self with stack := pushed }
            have htail_bits : BuilderMergeBits cursor (start + 1)
                remaining_count root_depth packing_depth := by
              constructor
              · intro offset hoffset
                have hmerge := hbits.merge (offset + 1) (by omega)
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  hmerge
              · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  hbits.stop
            apply ih htail_bits next_self next_index next_i result_stack
              result_depth result_level result_length result_factor
              result_packing_depth result_capacity
            · exact hdepth
            · exact hpacking_depth
            · exact hcursor
            · exact hi_next
            · exact hpushed_values
            · exact hloop

private theorem finish_level_loop_follows_merge_plan {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {count cursor start root_depth packing_depth : Nat}
    {input_stack : List (utils.MaybeArced (Tree T))} {input_top : Tree T}
    {final_stack : List (utils.MaybeArced (Tree T))}
    {final_top : Tree T} {final_depth final_len : Nat}
    (hplan : BuilderMergePlan ValueInst packing_factor count input_stack
      input_top final_stack final_top final_depth final_len)
    (hbits : BuilderMergeBits cursor start count root_depth packing_depth) :
    ∀ (self : builder.Builder T) (next_index_on_level i : Std.Usize)
      (result_stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
      (result_depth result_level : Std.Usize) (result_length : utils.Length)
      (result_factor : Option Std.Usize)
      (result_packing_depth result_capacity : Std.Usize),
      self.depth.val = root_depth →
      self.packing_depth.val = packing_depth →
      cursor = next_index_on_level.val * 2 ^ self.level.val →
      cursor < 2 ^ System.Platform.numBits →
      i.val = start →
      self.stack.val = input_stack ++
        [utils.MaybeArced.Unarced input_top] →
      builder.Builder.finish_level_loop ValueInst self next_index_on_level i =
        ok (core.result.Result.Ok (), result_stack, result_depth, result_level,
          result_length, result_factor, result_packing_depth,
          result_capacity) →
      result_stack.val = final_stack ++
          [utils.MaybeArced.Unarced final_top] ∧
        result_depth = self.depth ∧ result_level = self.level ∧
        result_length = self.length ∧ result_factor = self.packing_factor ∧
        result_packing_depth = self.packing_depth ∧
        result_capacity = self.capacity := by
  induction hplan generalizing start with
  | done plan_stack top depth len top_dense top_nonempty =>
    intro self next_index i result_stack result_depth result_level result_length
      result_factor result_packing_depth result_capacity hdepth hpacking_depth
      hcursor hcursor_fit hi hstack hloop
    rw [finish_level_loop_step] at hloop
    unfold builder.Builder.finish_level_loop.body at hloop
    by_cases hlt : i < self.depth
    · simp only [hlt, ↓reduceIte, bind_tc_ok] at hloop
      cases hleft : next_index <<< self.level with
      | fail error => simp [hleft] at hloop
      | div => simp [hleft] at hloop
      | ok shifted_cursor =>
        simp only [hleft, bind_tc_ok] at hloop
        cases hadd : i + self.packing_depth with
        | fail error => simp [hadd] at hloop
        | div => simp [hadd] at hloop
        | ok shift =>
          simp only [hadd, bind_tc_ok] at hloop
          cases hright : shifted_cursor >>> shift with
          | fail error => simp [hright] at hloop
          | div => simp [hright] at hloop
          | ok shifted =>
            have hcursor_value := usize_shift_left_value hleft hcursor
              hcursor_fit
            have hshift_value := usize_add_value hadd
            have hshifted_value := usize_shift_right_value hright
            have hmerge_stop := hbits.stop
            have hlt_value : start < root_depth := by scalar_tac
            have hstop_nat :
                ((cursor >>> (start + packing_depth)) &&& 1) = 0 := by
              rcases hmerge_stop with hroot | hbit
              · omega
              · simpa using hbit
            have hbit : (shifted &&& 1#usize) = 0#usize := by
              apply UScalar.eq_of_val_eq
              simpa [hshifted_value, hcursor_value, hshift_value, hi,
                hpacking_depth] using hstop_nat
            simp [hright, hbit] at hloop
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hloop
            exact ⟨hstack, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [hlt] at hloop
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hloop
      exact ⟨hstack, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | @step base_stack left top merged depth top_len remaining_count final_stack
      final_top final_depth final_len left_dense top_dense top_nonempty merge_eq
      remaining ih =>
    intro self next_index i result_stack result_depth result_level result_length
      result_factor result_packing_depth result_capacity hdepth hpacking_depth
      hcursor hcursor_fit hi hstack hloop
    have hmerge_zero := hbits.merge 0 (by omega)
    have hlt : i < self.depth := by scalar_tac
    rw [finish_level_loop_step] at hloop
    unfold builder.Builder.finish_level_loop.body at hloop
    simp only [hlt, ↓reduceIte, bind_tc_ok] at hloop
    cases hleft_shift : next_index <<< self.level with
    | fail error => simp [hleft_shift] at hloop
    | div => simp [hleft_shift] at hloop
    | ok shifted_cursor =>
      simp only [hleft_shift, bind_tc_ok] at hloop
      cases hadd_shift : i + self.packing_depth with
      | fail error => simp [hadd_shift] at hloop
      | div => simp [hadd_shift] at hloop
      | ok shift =>
        simp only [hadd_shift, bind_tc_ok] at hloop
        cases hright_shift : shifted_cursor >>> shift with
        | fail error => simp [hright_shift] at hloop
        | div => simp [hright_shift] at hloop
        | ok shifted =>
          have hcursor_value := usize_shift_left_value hleft_shift
            hcursor hcursor_fit
          have hshift_value := usize_add_value hadd_shift
          have hshifted_value := usize_shift_right_value hright_shift
          have hbit : (shifted &&& 1#usize) = 1#usize := by
            apply UScalar.eq_of_val_eq
            simpa [hshifted_value, hcursor_value, hshift_value, hi,
              hpacking_depth] using hmerge_zero.2
          have hsource_values : self.stack.val =
              (base_stack ++ [left]) ++
                [utils.MaybeArced.Unarced top] := hstack
          obtain ⟨after_top, hpop_top, hafter_top⟩ :=
            vec_pop_append_last (A := Global) self.stack
              (base_stack ++ [left]) (utils.MaybeArced.Unarced top)
              hsource_values
          obtain ⟨after_left, hpop_left, hafter_left⟩ :=
            vec_pop_append_last (A := Global) after_top base_stack left
              hafter_top
          simp [hright_shift, hbit, lift, hpop_top, hpop_left,
            core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            maybeArced_arced, merge_eq] at hloop
          cases hpush : alloc.vec.Vec.push after_left
              (utils.MaybeArced.Unarced merged) with
          | fail error => simp [hpush] at hloop
          | div => simp [hpush] at hloop
          | ok pushed =>
            simp only [hpush, bind_tc_ok] at hloop
            cases hnext : i + 1#usize with
            | fail error => simp [hnext] at hloop
            | div => simp [hnext] at hloop
            | ok next_i =>
              simp only [hnext, bind_tc_ok] at hloop
              have hpushed := vec_push_values after_left
                (utils.MaybeArced.Unarced merged) hpush
              have hpushed_values : pushed.val =
                  base_stack ++ [utils.MaybeArced.Unarced merged] := by
                simpa [hafter_left] using hpushed
              have hnext_value := usize_add_one_value hnext
              have hi_next : next_i.val = start + 1 := by omega
              let next_self := { self with stack := pushed }
              have htail_bits : BuilderMergeBits cursor (start + 1)
                  remaining_count root_depth packing_depth := by
                constructor
                · intro offset hoffset
                  have hmerge := hbits.merge (offset + 1) (by omega)
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    hmerge
                · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    hbits.stop
              apply ih htail_bits next_self next_index next_i result_stack
                result_depth result_level result_length result_factor
                result_packing_depth result_capacity
              · exact hdepth
              · exact hpacking_depth
              · exact hcursor
              · exact hcursor_fit
              · exact hi_next
              · exact hpushed_values
              · exact hloop

private theorem finish_tree_body_preserves_normalized {T : Type}
    {ValueInst : Value T} {self next_self : builder.Builder T}
    {next_index next_index1 : Std.Usize}
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hlevel_valid : self.level.val = 0 ∨
      self.packing_depth.val ≤ self.level.val)
    (hcapacity : self.capacity.val =
      subtreeCapacity self.packing_factor self.depth.val)
    (hroot_bits : self.depth.val + self.packing_depth.val <
      System.Platform.numBits)
    {base_depth logical_len physical_len : Nat}
    (hnormalized : BuilderNormalizedStack self.packing_factor base_depth
      self.stack.val self.depth.val logical_len physical_len)
    (hbase : base_depth = if self.level.val = 0 then 0
      else self.level.val - self.packing_depth.val)
    (hlogical : 0 < logical_len)
    (hphysical : physical_len < subtreeCapacity self.packing_factor
      self.depth.val)
    (hcursor : physical_len = next_index.val * 2 ^ self.level.val)
    (hbody : builder.Builder.finish_tree_loop.body ValueInst self next_index =
      ok (.cont (next_self, next_index1))) :
    ∃ (next_physical : Nat)
        (next_stack : alloc.vec.Vec (utils.MaybeArced (Tree T))),
      next_self.stack = next_stack ∧
      next_self.depth = self.depth ∧ next_self.level = self.level ∧
      next_self.length = self.length ∧
      next_self.packing_factor = self.packing_factor ∧
      next_self.packing_depth = self.packing_depth ∧
      next_self.capacity = self.capacity ∧
      BuilderNormalizedStack self.packing_factor base_depth
        (alloc.vec.Vec.v next_stack) self.depth.val logical_len next_physical ∧
      physical_len < next_physical ∧
      next_physical ≤ subtreeCapacity self.packing_factor self.depth.val ∧
      next_physical = next_index1.val * 2 ^ self.level.val := by
  obtain ⟨prefix_stack, top, top_depth, prefix_len, top_len, hstack,
      hbase_top, htop_depth, htop, htop_nonempty, hprefix, haligned,
      hlogical_len, hphysical_len⟩ :=
    hnormalized.split_last_of_not_full hlayout hlogical hphysical
  have hlevel_top : self.level.val ≤ top_depth + self.packing_depth.val := by
    rw [hbase] at hbase_top
    by_cases hlevel : self.level.val = 0
    · omega
    · have hpacking_le := hlevel_valid.resolve_left hlevel
      simp [hlevel] at hbase_top
      omega
  obtain ⟨units, hprefix_units⟩ :=
    Nat.dvd_of_mod_eq_zero haligned
  have hprefix_units' : prefix_len =
      subtreeCapacity self.packing_factor (top_depth + 1) * units := by
    simpa [Nat.mul_comm] using hprefix_units
  unfold builder.Builder.finish_tree_loop.body at hbody
  cases hshift : next_index <<< self.level with
  | fail error => simp [hshift] at hbody
  | div => simp [hshift] at hbody
  | ok shifted_cursor =>
    simp only [hshift, bind_tc_ok] at hbody
    have hcursor_fit : physical_len < 2 ^ System.Platform.numBits := by
      exact hphysical.trans_le (by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        have hbits : self.packing_depth.val + self.depth.val <
            System.Platform.numBits := by
          have := hroot_bits
          omega
        exact Nat.le_of_lt (Nat.pow_lt_pow_right (by omega)
          hbits))
    have hshift_value := usize_shift_left_value hshift hcursor
      hcursor_fit
    have hnot_done : shifted_cursor ≠ self.capacity := by
      intro heq
      have heq_val := congrArg UScalar.val heq
      omega
    have hcontinue : (shifted_cursor != self.capacity) = true := by
      simp [hnot_done]
    rw [hcontinue] at hbody
    simp only [↓reduceIte] at hbody
    cases hzeros : core.num.Usize.trailing_zeros next_index with
    | fail error => simp [hzeros] at hbody
    | div => simp [hzeros] at hbody
    | ok zeros =>
      simp only [hzeros, bind_tc_ok, lift] at hbody
      let depth := core.num.Usize.saturating_sub
        (core.num.Usize.saturating_add (UScalar.cast .Usize zeros) self.level)
        self.packing_depth
      have hdepth : depth.val = top_depth := by
        apply finish_top_depth_eq hlayout hprefix_units' htop_depth
          hphysical_len hcursor hlevel_top hroot_bits
          hzeros
      cases hpop : alloc.vec.Vec.pop Global self.stack with
      | fail error => simp [depth, hpop] at hbody
      | div => simp [depth, hpop] at hbody
      | ok pop_result =>
        obtain ⟨popped, popped_stack⟩ := pop_result
        simp only [depth, hpop, bind_tc_ok] at hbody
        cases popped with
        | none =>
          obtain ⟨expected_stack, hpop_expected, hexpected_stack⟩ :=
            vec_pop_append_last (A := Global) self.stack prefix_stack top
              hstack
          rw [hpop] at hpop_expected
          simp at hpop_expected
        | some popped_top =>
          have hpopped_values := vec_pop_some_values
            (A := Global) self.stack popped_stack popped_top hpop
          rw [hstack] at hpopped_values
          have hlength : prefix_stack.length = popped_stack.val.length := by
            have := congrArg List.length hpopped_values
            simp at this
            omega
          have hparts := List.append_inj hpopped_values hlength
          obtain ⟨hpopped_stack, hpopped_top⟩ := hparts
          simp at hpopped_top
          subst popped_top
          simp [core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch] at hbody
          cases hzero : Tree.zero ValueInst depth with
          | fail error =>
            change Tree.zero ValueInst
              (core.num.Usize.saturating_sub
                (core.num.Usize.saturating_add
                  (UScalar.cast .Usize zeros) self.level)
                self.packing_depth) = fail error at hzero
            simp [hzero] at hbody
          | div =>
            change Tree.zero ValueInst
              (core.num.Usize.saturating_sub
                (core.num.Usize.saturating_add
                  (UScalar.cast .Usize zeros) self.level)
                self.packing_depth) = div at hzero
            simp [hzero] at hbody
          | ok zero =>
            change Tree.zero ValueInst
              (core.num.Usize.saturating_sub
                (core.num.Usize.saturating_add
                  (UScalar.cast .Usize zeros) self.level)
                self.packing_depth) = ok zero at hzero
            simp only [hzero, bind_tc_ok] at hbody
            cases hpad : Tree.node_unboxed ValueInst (maybeArcedTree top) zero with
            | fail error => simp [hpad] at hbody
            | div => simp [hpad] at hbody
            | ok padded =>
              simp only [hpad, bind_tc_ok] at hbody
              cases hpush : alloc.vec.Vec.push popped_stack
                  (utils.MaybeArced.Unarced padded) with
              | fail error => simp [hpush] at hbody
              | div => simp [hpush] at hbody
              | ok padded_stack =>
                simp only [hpush, bind_tc_ok] at hbody
                obtain ⟨zero_result, hzero_result, hzero_dense⟩ :=
                  zero_preserves_dense ValueInst self.packing_factor depth
                rw [hzero] at hzero_result
                cases hzero_result
                have hzero_dense' : DenseTree self.packing_factor zero
                    top_depth 0 := by simpa [hdepth] using hzero_dense
                have hpadded_stack := vec_push_values popped_stack
                  (utils.MaybeArced.Unarced padded) hpush
                have hpadded_values : padded_stack.val =
                    prefix_stack ++ [utils.MaybeArced.Unarced padded] := by
                  rw [hpadded_stack, ← hpopped_stack]
                obtain ⟨count, final_stack, final_top, final_depth, final_len,
                    hplan, hcarry, hnext_normalized⟩ :=
                  hprefix.finish_padding_plan hlayout
                    (Nat.le_succ_of_le hbase_top) haligned htop
                    htop_nonempty hzero_dense' hpad hlogical_len
                    hphysical_len hnormalized.physical_le_capacity
                have hmerge_bits := hcarry.finish_merge_bits hlayout
                  hphysical_len
                let padded_self : builder.Builder T :=
                  { self with stack := padded_stack }
                cases hfinish : builder.Builder.finish_level ValueInst
                    padded_self next_index depth with
                | fail error =>
                  dsimp [padded_self, depth] at hfinish
                  simp [hfinish] at hbody
                | div =>
                  dsimp [padded_self, depth] at hfinish
                  simp [hfinish] at hbody
                | ok finish_result =>
                  obtain ⟨finish_status, finished_self⟩ := finish_result
                  dsimp [padded_self, depth] at hfinish
                  simp only [hfinish, bind_tc_ok] at hbody
                  cases finish_status with
                  | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hbody
                  | Ok success =>
                    cases success
                    have hfinish_spec := hfinish
                    unfold builder.Builder.finish_level at hfinish_spec
                    cases hstart : depth + 1#usize with
                    | fail error =>
                      dsimp [depth] at hstart
                      simp [hstart] at hfinish_spec
                    | div =>
                      dsimp [depth] at hstart
                      simp [hstart] at hfinish_spec
                    | ok start_i =>
                      dsimp [depth] at hstart
                      simp only [hstart, bind_tc_ok] at hfinish_spec
                      cases hlevel_loop : builder.Builder.finish_level_loop
                          ValueInst
                          { stack := padded_stack, depth := self.depth,
                            level := self.level, length := self.length,
                            packing_factor := self.packing_factor,
                            packing_depth := self.packing_depth,
                            capacity := self.capacity }
                          next_index start_i with
                      | fail error => simp [hlevel_loop] at hfinish_spec
                      | div => simp [hlevel_loop] at hfinish_spec
                      | ok loop_result =>
                        obtain ⟨loop_status, loop_stack, loop_depth, loop_level,
                          loop_length, loop_factor, loop_packing_depth,
                          loop_capacity⟩ := loop_result
                        simp [hlevel_loop] at hfinish_spec
                        have hstart_value := usize_add_one_value hstart
                        have hstart_top : start_i.val = top_depth + 1 := by
                          rw [hstart_value]
                          change depth.val + 1 = top_depth + 1
                          rw [hdepth]
                        have hlevel_loop_ok :
                            builder.Builder.finish_level_loop ValueInst
                              { stack := padded_stack, depth := self.depth,
                                level := self.level, length := self.length,
                                packing_factor := self.packing_factor,
                                packing_depth := self.packing_depth,
                                capacity := self.capacity }
                              next_index start_i =
                            ok (core.result.Result.Ok (), loop_stack,
                              loop_depth, loop_level, loop_length, loop_factor,
                              loop_packing_depth, loop_capacity) := by
                          simpa [hfinish_spec.1] using hlevel_loop
                        have hlevel_result :=
                          finish_level_loop_follows_merge_plan hplan
                            hmerge_bits
                            { stack := padded_stack, depth := self.depth,
                              level := self.level, length := self.length,
                              packing_factor := self.packing_factor,
                              packing_depth := self.packing_depth,
                              capacity := self.capacity }
                            next_index start_i loop_stack loop_depth loop_level
                            loop_length loop_factor loop_packing_depth
                            loop_capacity rfl rfl hcursor hcursor_fit
                            hstart_top hpadded_values hlevel_loop_ok
                        obtain ⟨hloop_stack, hloop_depth, hloop_level,
                          hloop_length, hloop_factor, hloop_packing_depth,
                          hloop_capacity⟩ := hlevel_result
                        have hfinished : finished_self =
                            { stack := loop_stack, depth := self.depth,
                              level := self.level, length := self.length,
                              packing_factor := self.packing_factor,
                              packing_depth := self.packing_depth,
                              capacity := self.capacity } := by
                          rw [← hfinish_spec.2, hloop_depth, hloop_level,
                            hloop_length, hloop_factor, hloop_packing_depth,
                            hloop_capacity]
                        rw [hfinished] at hbody
                        simp at hbody
                        cases hadd_depth : depth + self.packing_depth with
                        | fail error =>
                          dsimp [depth] at hadd_depth
                          simp [hadd_depth] at hbody
                        | div =>
                          dsimp [depth] at hadd_depth
                          simp [hadd_depth] at hbody
                        | ok depth_with_packing =>
                          dsimp [depth] at hadd_depth
                          simp only [hadd_depth, bind_tc_ok] at hbody
                          cases hsub_level : depth_with_packing - self.level with
                          | fail error => simp [hsub_level] at hbody
                          | div => simp [hsub_level] at hbody
                          | ok increment_exponent =>
                            simp only [hsub_level, bind_tc_ok] at hbody
                            cases hpow : core.num.Usize.pow 2#usize
                                (UScalar.cast .U32 increment_exponent) with
                            | fail error => simp [hpow] at hbody
                            | div => simp [hpow] at hbody
                            | ok increment =>
                              simp only [hpow, bind_tc_ok] at hbody
                              cases hnext : next_index + increment with
                              | fail error => simp [hnext] at hbody
                              | div => simp [hnext] at hbody
                              | ok next_index' =>
                                simp [hnext] at hbody
                                obtain ⟨rfl, rfl⟩ := hbody
                                have hadd_depth_value :=
                                  usize_add_value hadd_depth
                                have hsub_level_value :=
                                  UScalar.sub_equiv depth_with_packing self.level
                                rw [hsub_level] at hsub_level_value
                                obtain ⟨-, hsub_value, -⟩ := hsub_level_value
                                have hdepth_with_packing :
                                    depth_with_packing.val = top_depth +
                                      self.packing_depth.val := by
                                  rw [hadd_depth_value]
                                  change depth.val + self.packing_depth.val = _
                                  rw [hdepth]
                                have hincrement_exponent :
                                    increment_exponent.val = top_depth +
                                      self.packing_depth.val - self.level.val := by
                                  omega
                                have hexponent_u32 : increment_exponent.val <
                                    2 ^ 32 := by
                                  rw [hincrement_exponent]
                                  have hbits_u32 : System.Platform.numBits <
                                      2 ^ 32 := by native_decide
                                  omega
                                have hcast_exponent := usize_cast_u32_value
                                  increment_exponent hexponent_u32
                                have hincrement := usize_pow_two_value hpow
                                rw [hcast_exponent, hincrement_exponent] at hincrement
                                have hnext_value := usize_add_value hnext
                                have hcapacity_top :=
                                  hlayout.subtreeCapacity_eq_two_pow top_depth
                                let next_physical := physical_len +
                                  subtreeCapacity self.packing_factor top_depth
                                have hnext_cursor : next_physical =
                                    next_index'.val * 2 ^ self.level.val := by
                                  dsimp [next_physical]
                                  rw [hnext_value, hincrement, Nat.add_mul,
                                    ← hcursor, hcapacity_top]
                                  have hexponent_sum :
                                      (top_depth + self.packing_depth.val -
                                          self.level.val) + self.level.val =
                                        self.packing_depth.val + top_depth := by
                                    omega
                                  rw [← pow_add, hexponent_sum]
                                refine ⟨next_physical, loop_stack, rfl, rfl, rfl,
                                  rfl, rfl, rfl, rfl, ?_, ?_, ?_, hnext_cursor⟩
                                · simpa [next_physical, hloop_stack] using
                                    hnext_normalized
                                · dsimp [next_physical]
                                  have hcap_pos :=
                                    hlayout.subtreeCapacity_pos top_depth
                                  omega
                                · dsimp [next_physical]
                                  exact hnext_normalized.physical_le_capacity

private theorem finish_tree_loop_completes_normalized {T : Type}
    {ValueInst : Value T} {self result : builder.Builder T}
    {next_index : Std.Usize}
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hlevel_valid : self.level.val = 0 ∨
      self.packing_depth.val ≤ self.level.val)
    (hcapacity : self.capacity.val =
      subtreeCapacity self.packing_factor self.depth.val)
    (hroot_bits : self.depth.val + self.packing_depth.val <
      System.Platform.numBits)
    {base_depth logical_len physical_len : Nat}
    (hnormalized : BuilderNormalizedStack self.packing_factor base_depth
      self.stack.val self.depth.val logical_len physical_len)
    (hbase : base_depth = if self.level.val = 0 then 0
      else self.level.val - self.packing_depth.val)
    (hlogical : 0 < logical_len)
    (hcursor : physical_len = next_index.val * 2 ^ self.level.val)
    (hloop : builder.Builder.finish_tree_loop ValueInst self next_index =
      ok (core.result.Result.Ok (), result)) :
    result.depth = self.depth ∧ result.level = self.level ∧
      result.length = self.length ∧
      result.packing_factor = self.packing_factor ∧
      result.packing_depth = self.packing_depth ∧
      result.capacity = self.capacity ∧
      BuilderNormalizedStack self.packing_factor base_depth result.stack.val
        self.depth.val logical_len
        (subtreeCapacity self.packing_factor self.depth.val) := by
  let capacity := subtreeCapacity self.packing_factor self.depth.val
  have hphysical_le : physical_len ≤ capacity := by
    exact hnormalized.physical_le_capacity
  have hcapacity_fit : capacity < 2 ^ System.Platform.numBits := by
    dsimp [capacity]
    rw [hlayout.subtreeCapacity_eq_two_pow]
    have hbits : self.packing_depth.val + self.depth.val <
        System.Platform.numBits := by omega
    exact Nat.pow_lt_pow_right (by omega) hbits
  generalize hremaining : capacity - physical_len = remaining
  induction remaining using Nat.strong_induction_on generalizing self next_index
      physical_len result with
  | h current_gap ih =>
    rw [finish_tree_loop_step] at hloop
    cases hbody : builder.Builder.finish_tree_loop.body ValueInst self
        next_index with
    | fail error => simp [hbody] at hloop
    | div => simp [hbody] at hloop
    | ok flow =>
      cases flow with
      | done done_result =>
        obtain ⟨status, done_self⟩ := done_result
        simp [hbody] at hloop
        obtain ⟨rfl, rfl⟩ := hloop
        obtain ⟨hfull, rfl⟩ := finish_tree_body_done_ok_eq_capacity
          hcapacity hcursor (hphysical_le.trans_lt hcapacity_fit) hbody
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        simpa [hfull] using hnormalized
      | cont next_state =>
        obtain ⟨next_self, next_index1⟩ := next_state
        simp [hbody] at hloop
        have hphysical_lt : physical_len < capacity := by
          exact finish_tree_body_cont_lt_capacity hcapacity hphysical_le
            hcursor (hphysical_le.trans_lt hcapacity_fit) hbody
        obtain ⟨next_physical, next_stack, hnext_stack, hnext_depth,
            hnext_level, hnext_length, hnext_factor, hnext_packing_depth,
            hnext_capacity, hnext_normalized, hphysical_next,
            hnext_le, hnext_cursor⟩ :=
          finish_tree_body_preserves_normalized hlayout hlevel_valid hcapacity
            hroot_bits hnormalized hbase hlogical hphysical_lt hcursor hbody
        have hlayout_next : PackingLayout ValueInst next_self.packing_factor
            next_self.packing_depth := by
          simpa [hnext_factor, hnext_packing_depth] using hlayout
        have hlevel_valid_next : next_self.level.val = 0 ∨
            next_self.packing_depth.val ≤ next_self.level.val := by
          simpa [hnext_level, hnext_packing_depth] using hlevel_valid
        have hcapacity_next : next_self.capacity.val =
            subtreeCapacity next_self.packing_factor next_self.depth.val := by
          simpa [hnext_capacity, hnext_factor, hnext_depth] using hcapacity
        have hroot_bits_next : next_self.depth.val +
            next_self.packing_depth.val < System.Platform.numBits := by
          simpa [hnext_depth, hnext_packing_depth] using hroot_bits
        have hbase_next : base_depth = if next_self.level.val = 0 then 0
            else next_self.level.val - next_self.packing_depth.val := by
          simpa [hnext_level, hnext_packing_depth] using hbase
        have hnext_normalized' : BuilderNormalizedStack
            next_self.packing_factor base_depth next_self.stack.val
            next_self.depth.val logical_len next_physical := by
          simpa [hnext_stack, hnext_factor, hnext_depth] using hnext_normalized
        have hnext_cursor' : next_physical =
            next_index1.val * 2 ^ next_self.level.val := by
          simpa [hnext_level] using hnext_cursor
        have hnext_le' : next_physical ≤ subtreeCapacity
            next_self.packing_factor next_self.depth.val := by
          simpa [hnext_factor, hnext_depth] using hnext_le
        have hcapacity_fit_next : subtreeCapacity next_self.packing_factor
            next_self.depth.val < 2 ^ System.Platform.numBits := by
          simpa [hnext_factor, hnext_depth] using hcapacity_fit
        have hgap_next : capacity - next_physical < current_gap := by
          omega
        have hremaining_next : subtreeCapacity next_self.packing_factor
            next_self.depth.val - next_physical =
              capacity - next_physical := by
          simp [hnext_factor, hnext_depth, capacity]
        have hrecursive := ih (capacity - next_physical) hgap_next
          hlayout_next hlevel_valid_next hcapacity_next hroot_bits_next
          hnext_normalized' hbase_next hnext_cursor' hloop hnext_le'
          hcapacity_fit_next hremaining_next
        obtain ⟨hresult_depth, hresult_level, hresult_length,
          hresult_factor, hresult_packing_depth, hresult_capacity,
          hresult_normalized⟩ := hrecursive
        refine ⟨hresult_depth.trans hnext_depth,
          hresult_level.trans hnext_level,
          hresult_length.trans hnext_length,
          hresult_factor.trans hnext_factor,
          hresult_packing_depth.trans hnext_packing_depth,
          hresult_capacity.trans hnext_capacity, ?_⟩
        simpa [hnext_factor, hnext_depth] using hresult_normalized

private theorem finish_packed_leaf_normalizes_partial {T : Type}
    {ValueInst : Value T} {self result : builder.Builder T}
    {next_index : Std.Usize}
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hstack : BuilderStack self.packing_factor 0 self.stack.val
      self.depth.val self.length.val)
    {prefix_stack : List (utils.MaybeArced (Tree T))} {top : Tree T}
    {top_len : Nat}
    (hentries : self.stack.val = prefix_stack ++
      [utils.MaybeArced.Unarced top])
    (htop : DenseTree self.packing_factor top 0 top_len)
    (htop_nonempty : 0 < top_len)
    (htop_partial : top_len < subtreeCapacity self.packing_factor 0)
    (hcursor : self.length.val = next_index.val)
    (hfinish : builder.Builder.finish_packed_leaf ValueInst self next_index =
      ok (core.result.Result.Ok (), result)) :
    ∃ prefix_len,
      self.length.val = prefix_len + top_len ∧
      prefix_len % subtreeCapacity self.packing_factor 0 = 0 ∧
      result.depth = self.depth ∧ result.level = self.level ∧
      result.length = self.length ∧
      result.packing_factor = self.packing_factor ∧
      result.packing_depth = self.packing_depth ∧
      result.capacity = self.capacity ∧
      BuilderNormalizedStack self.packing_factor 0 result.stack.val
        self.depth.val self.length.val
        (prefix_len + subtreeCapacity self.packing_factor 0) := by
  obtain ⟨prefix_len, hlength, haligned, hprefix⟩ :=
    hstack.remove_partial_last hlayout hentries htop htop_nonempty
      htop_partial
  have hfits : prefix_len + top_len ≤
      subtreeCapacity self.packing_factor self.depth.val := by
    have := hstack.length_le_capacity
    omega
  obtain ⟨count, final_stack, final_top, final_depth, final_len, hplan,
      hcarry, hcanonical, hnormalized, hfull⟩ :=
    hprefix.append_subtree hlayout htop htop_nonempty haligned hfits
  have hbits := hcarry.finish_partial_merge_bits hlayout
    (cursor := self.length.val) hlength htop_partial
  unfold builder.Builder.finish_packed_leaf at hfinish
  cases hloop : builder.Builder.finish_packed_leaf_loop ValueInst self
      next_index 0#usize with
  | fail error => simp [hloop] at hfinish
  | div => simp [hloop] at hfinish
  | ok loop_result =>
    obtain ⟨status, result_stack, result_depth, result_level, result_length,
      result_factor, result_packing_depth, result_capacity⟩ := loop_result
    simp only [hloop, bind_tc_ok] at hfinish
    obtain ⟨rfl, rfl⟩ := hfinish
    obtain ⟨hresult_stack, hresult_depth, hresult_level, hresult_length,
      hresult_factor, hresult_packing_depth, hresult_capacity⟩ :=
      finish_packed_leaf_loop_follows_merge_plan hplan hbits self next_index
        0#usize result_stack result_depth result_level result_length
        result_factor result_packing_depth result_capacity rfl rfl hcursor
        rfl hentries hloop
    refine ⟨prefix_len, hlength, haligned, hresult_depth, hresult_level,
      hresult_length, hresult_factor, hresult_packing_depth, hresult_capacity,
      ?_⟩
    simpa [hresult_stack, hlength] using hnormalized

private theorem finish_tree_completed_entry_dense {T : Type}
    {ValueInst : Value T} {self finished : builder.Builder T}
    {next_index : Std.Usize}
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hlevel_valid : self.level.val = 0 ∨
      self.packing_depth.val ≤ self.level.val)
    (hcapacity : self.capacity.val =
      subtreeCapacity self.packing_factor self.depth.val)
    (hroot_bits : self.depth.val + self.packing_depth.val <
      System.Platform.numBits)
    {base_depth logical_len physical_len : Nat}
    (hnormalized : BuilderNormalizedStack self.packing_factor base_depth
      self.stack.val self.depth.val logical_len physical_len)
    (hbase : base_depth = if self.level.val = 0 then 0
      else self.level.val - self.packing_depth.val)
    (hlogical : 0 < logical_len)
    (hcursor : physical_len = next_index.val * 2 ^ self.level.val)
    (hfinish : builder.Builder.finish_tree ValueInst self next_index =
      ok (core.result.Result.Ok (), finished))
    {entry : utils.MaybeArced (Tree T)}
    {rest : alloc.vec.Vec (utils.MaybeArced (Tree T))} {tree : Tree T}
    (hpop : alloc.vec.Vec.pop Global finished.stack =
      ok (some entry, rest))
    (harced : utils.MaybeArced.arced entry = ok tree) :
    finished.depth = self.depth ∧ finished.length = self.length ∧
      DenseTree self.packing_factor tree self.depth.val logical_len := by
  have hcompleted := finish_tree_loop_completes_normalized hlayout
    hlevel_valid hcapacity hroot_bits hnormalized hbase hlogical hcursor
    hfinish
  obtain ⟨hdepth, hlevel, hlength, hfactor, hpacking_depth, hcapacity',
      hfinished⟩ := hcompleted
  obtain ⟨expected, hstack, hdense⟩ :=
    hfinished.full_physical_singleton hlayout hlogical rfl
  have hpopped := vec_pop_some_values (A := Global) finished.stack rest entry
    hpop
  rw [hstack] at hpopped
  have hrest_length_succ : rest.val.length + 1 = 1 := by
    simpa using congrArg List.length hpopped.symm
  have hrest_length : rest.val.length = 0 := by omega
  have hrest : rest.val = [] := List.eq_nil_of_length_eq_zero hrest_length
  have hentry : entry = expected := by
    simpa [hrest] using hpopped.symm
  subst entry
  have htree : tree = maybeArcedTree expected := by
    simpa using harced.symm
  exact ⟨hdepth, hlength, by simpa [htree] using hdense⟩

private def finishTreeAndFinalize {T : Type} (ValueInst : Value T)
    (self : builder.Builder T) (next_index : Std.Usize) :
    Result (core.result.Result
      ((triomphe.arc.Arc (Tree T)) × Std.Usize × utils.Length)
      error.Error) := do
  let (r, finished) ←
    builder.Builder.finish_tree ValueInst self next_index
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (entry, rest) ← alloc.vec.Vec.pop Global finished.stack
    let r1 ← core.option.Option.ok_or entry
      error.Error.BuilderStackEmptyFinalize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue entry =>
      let tree ← utils.MaybeArced.arced entry
      let empty ← alloc.vec.Vec.is_empty Global rest
      if empty then
        ok (core.result.Result.Ok (tree, finished.depth, finished.length))
      else ok (core.result.Result.Err error.Error.BuilderStackLeftover)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((triomphe.arc.Arc (Tree T)) × Std.Usize × utils.Length)
        (core.convert.FromSame error.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((triomphe.arc.Arc (Tree T)) × Std.Usize × utils.Length)
      (core.convert.FromSame error.Error) residual

private theorem finish_tree_and_finalize_returns_dense {T : Type}
    {ValueInst : Value T} {self : builder.Builder T}
    {next_index : Std.Usize}
    (hlayout : PackingLayout ValueInst self.packing_factor self.packing_depth)
    (hlevel_valid : self.level.val = 0 ∨
      self.packing_depth.val ≤ self.level.val)
    (hcapacity : self.capacity.val =
      subtreeCapacity self.packing_factor self.depth.val)
    (hroot_bits : self.depth.val + self.packing_depth.val <
      System.Platform.numBits)
    {base_depth logical_len physical_len : Nat}
    (hnormalized : BuilderNormalizedStack self.packing_factor base_depth
      self.stack.val self.depth.val logical_len physical_len)
    (hbase : base_depth = if self.level.val = 0 then 0
      else self.level.val - self.packing_depth.val)
    (hlogical : 0 < logical_len)
    (hcursor : physical_len = next_index.val * 2 ^ self.level.val)
    {tree : Tree T} {depth : Std.Usize} {length : utils.Length}
    (hfinish : finishTreeAndFinalize ValueInst self next_index =
      ok (core.result.Result.Ok (tree, depth, length))) :
    depth = self.depth ∧ length = self.length ∧
      DenseTree self.packing_factor tree self.depth.val logical_len := by
  unfold finishTreeAndFinalize at hfinish
  cases htree : builder.Builder.finish_tree ValueInst self next_index with
  | fail error => simp [htree] at hfinish
  | div => simp [htree] at hfinish
  | ok finish_result =>
    obtain ⟨status, finished⟩ := finish_result
    cases status with
    | Err error =>
      simp [htree, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at hfinish
    | Ok success =>
      cases success
      simp only [htree, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        at hfinish
      cases hpop : alloc.vec.Vec.pop Global finished.stack with
      | fail error => simp [hpop] at hfinish
      | div => simp [hpop] at hfinish
      | ok pop_result =>
        obtain ⟨entry, rest⟩ := pop_result
        cases entry with
        | none =>
          simp [hpop, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at hfinish
        | some entry =>
          simp only [hpop, bind_tc_ok, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch] at hfinish
          cases hempty : alloc.vec.Vec.is_empty Global rest with
          | fail error => simp [hpop, hempty] at hfinish
          | div => simp [hpop, hempty] at hfinish
          | ok empty =>
            cases empty with
            | false => simp [hpop, hempty] at hfinish
            | true =>
              simp [hpop, hempty] at hfinish
              obtain ⟨rfl, rfl, rfl⟩ := hfinish
              exact finish_tree_completed_entry_dense hlayout hlevel_valid
                hcapacity hroot_bits hnormalized hbase hlogical hcursor
                htree hpop (maybeArced_arced entry)

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
                    hplan, hcarry, hcanonical, hnormalized, _⟩ :=
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
                have hnormalized_final : BuilderNormalizedStack
                    self.packing_factor
                    (if self.level.val = 0 then 0
                      else self.level.val - self.packing_depth.val)
                    final_stack.val self.depth.val
                    (self.length.val + len.val)
                    (self.length.val + subtreeCapacity self.packing_factor
                      (if self.level.val = 0 then 0
                        else self.level.val - self.packing_depth.val)) := by
                  apply hnormalized.rewrap
                  rw [hfinal_stack, hloop_stack]
                  simp [hloop_top]
                refine ⟨@BuilderInvariant.layout T ValueInst self hinvariant,
                  @BuilderInvariant.level_valid T ValueInst self hinvariant,
                  @BuilderInvariant.level_bounded T ValueInst self hinvariant,
                  @BuilderInvariant.builder_capacity_matches T ValueInst self
                    hinvariant, ?_, ?_, ?_⟩
                · simpa [hnew_length] using hcanonical_final
                · intro _
                  let base_capacity := subtreeCapacity self.packing_factor
                    (if self.level.val = 0 then 0
                      else self.level.val - self.packing_depth.val)
                  refine ⟨self.length.val + base_capacity, ?_, ?_, ?_, ?_⟩
                  · simpa [base_capacity, hnew_length] using
                      hnormalized_final
                  · simp [base_capacity, Nat.add_mod, haligned]
                  · have hnode_fit := hnode.length_le_capacity
                    simp [base_capacity]
                    omega
                  · simp [base_capacity]
                    omega
                · intro hlevel_zero hpartial
                  have hfactor_none : self.packing_factor = none :=
                    hnode_level.resolve_left (not_not.mpr hlevel_zero)
                  have : new_length.val % 1 = 0 := Nat.mod_one _
                  exact (hpartial (by simpa [hfactor_none, subtreeCapacity,
                    leafCapacity] using this)).elim

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

private theorem push_loop_preserves_builder_stack {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {base_depth root_depth old_len new_len count : Nat}
    {input_stack : List (utils.MaybeArced (Tree T))} {input_top : Tree T}
    {plan_stack : List (utils.MaybeArced (Tree T))}
    {plan_top : Tree T} {plan_depth plan_len : Nat}
    (hplan : BuilderMergePlan ValueInst packing_factor count input_stack
      input_top plan_stack plan_top plan_depth plan_len)
    (hcanonical : BuilderStack packing_factor base_depth
      (plan_stack ++ [utils.MaybeArced.Unarced plan_top]) root_depth new_len)
    (values_to_merge : Std.U32) (hcount : values_to_merge.val = count)
    (stack : alloc.vec.Vec (utils.MaybeArced (Tree T)))
    (length : utils.Length)
    {result_stack : alloc.vec.Vec (utils.MaybeArced (Tree T))}
    {result_length : utils.Length}
    (hstack : stack.val = input_stack)
    (hlength : length.val = old_len)
    (hloop : builder.Builder.push_loop0 ValueInst
      { start := 0#u32, «end» := values_to_merge } stack length input_top =
        ok (core.result.Result.Ok (), result_stack, result_length)) :
    BuilderStack packing_factor base_depth result_stack.val root_depth new_len ∧
      result_length.val = old_len + 1 := by
  obtain ⟨hresult_stack, hresult_length⟩ :=
    push_loop0_follows_merge_plan hplan
      { start := 0#u32, «end» := values_to_merge } stack length result_stack
      result_length (by simp [hcount]) hstack hloop
  rw [hresult_stack]
  exact ⟨hcanonical, by omega⟩

/-- Successful public value insertion preserves the Builder invariant. The
    sole extra premise says this is the public leaf-level Builder mode; every
    branch-specific alignment and capacity fact is recovered from the
    invariant and the successful translated call. -/
theorem builder_push_preserves_invariant {T : Type}
    {ValueInst : Value T} {self result : builder.Builder T}
    (hinvariant : BuilderInvariant ValueInst self)
    (hlevel : self.level.val = 0)
    (value : T)
    (hpush : builder.Builder.push ValueInst self value =
      ok (core.result.Result.Ok (), result)) :
    BuilderInvariant ValueInst result := by
  unfold builder.Builder.push at hpush
  simp only [utils.Length.as_usize, bind_tc_ok] at hpush
  by_cases hfull : self.length = self.capacity
  · rw [if_pos hfull] at hpush
    simp at hpush
  · rw [if_neg hfull] at hpush
    cases hnext : self.length + 1#usize with
    | fail error => simp [hnext] at hpush
    | div => simp [hnext] at hpush
    | ok next_index =>
      simp only [hnext, bind_tc_ok] at hpush
      cases hfactor : self.packing_factor with
      | none =>
        rw [hfactor] at hpush
        cases hleaf : Tree.leaf_unboxed ValueInst value with
        | fail error => simp [hleaf] at hpush
        | div => simp [hleaf] at hpush
        | ok leaf =>
          simp only [hleaf, bind_tc_ok, lift] at hpush
          cases hzeros : core.num.Usize.trailing_zeros next_index with
          | fail error => simp [hzeros] at hpush
          | div => simp [hzeros] at hpush
          | ok zeros =>
            simp only [hzeros, bind_tc_ok] at hpush
            let values_to_merge := core.num.U32.saturating_sub zeros
              (UScalar.cast .U32 self.packing_depth)
            cases hloop : builder.Builder.push_loop0 ValueInst
                { start := 0#u32, «end» := values_to_merge } self.stack
                self.length leaf with
            | fail error => simp [values_to_merge, hloop] at hpush
            | div => simp [values_to_merge, hloop] at hpush
            | ok loop_result =>
              obtain ⟨loop_status, loop_stack, loop_length⟩ := loop_result
              simp [values_to_merge, hloop] at hpush
              obtain ⟨rfl, rfl⟩ := hpush
              have hlayout : PackingLayout ValueInst none
                  self.packing_depth := by
                simpa [hfactor] using
                  (@BuilderInvariant.layout T ValueInst self hinvariant)
              have hstack : BuilderStack none 0 self.stack.val self.depth.val
                  self.length.val := by
                simpa [hfactor, hlevel] using
                  (@BuilderInvariant.stack_dense T ValueInst self hinvariant)
              obtain ⟨produced_leaf, hproduced, hleaf_dense⟩ :=
                leaf_unboxed_preserves_dense ValueInst value
              rw [hleaf] at hproduced
              cases hproduced
              have hlength_le := hinvariant.length_le_capacity
              have hlength_ne : self.length.val ≠ self.capacity.val := by
                intro heq
                exact hfull (UScalar.eq_of_val_eq heq)
              have hcapacity : self.capacity.val =
                  subtreeCapacity none self.depth.val := by
                simpa [hfactor] using
                  (@BuilderInvariant.builder_capacity_matches T ValueInst
                    self hinvariant)
              have hfits : self.length.val + 1 ≤
                  subtreeCapacity none self.depth.val := by
                rw [← hcapacity]
                omega
              obtain ⟨count, plan_stack, plan_top, plan_depth, plan_len,
                  hplan, hcarry, hcanonical, _⟩ :=
                hstack.append_subtree hlayout hleaf_dense (by omega)
                  (by exact Nat.mod_one _) hfits
              have hnext_value := usize_add_one_value hnext
              have hnext_cursor : next_index.val = self.length.val +
                  subtreeCapacity none 0 := by
                simpa [subtreeCapacity, leafCapacity] using hnext_value
              have hmerge_count : values_to_merge.val = count := by
                exact push_full_base_merge_count_eq hlayout hcarry
                  hnext_cursor hzeros
              obtain ⟨hresult_stack, hresult_length⟩ :=
                push_loop_preserves_builder_stack hplan hcanonical
                  values_to_merge hmerge_count self.stack self.length rfl rfl
                  hloop
              refine ⟨hlayout,
                @BuilderInvariant.level_valid T ValueInst self hinvariant,
                @BuilderInvariant.level_bounded T ValueInst self hinvariant,
                hcapacity, ?_, ?_, ?_⟩
              · simpa [hlevel, hresult_length] using hresult_stack
              · intro hready
                rcases hready with hlevel_ne | haligned
                · exact (hlevel_ne hlevel).elim
                · have hcursor :=
                    hresult_stack.normalized_cursor_of_aligned hlayout
                      (by simpa [hlevel, hresult_length] using haligned)
                  simpa [hlevel, hresult_length] using hcursor
              · intro _ hpartial
                exact (hpartial (Nat.mod_one _)).elim
      | some factor =>
        rw [hfactor] at hpush
        cases hmultiple : core.num.Usize.is_multiple_of self.length factor with
        | fail error => simp [hmultiple] at hpush
        | div => simp [hmultiple] at hpush
        | ok multiple =>
          simp only [hmultiple, bind_tc_ok] at hpush
          cases multiple with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at hpush
            cases hpop : alloc.vec.Vec.pop Global self.stack with
            | fail error => simp [hpop] at hpush
            | div => simp [hpop] at hpush
            | ok pop_result =>
              obtain ⟨popped, base_stack⟩ := pop_result
              simp only [hpop, bind_tc_ok] at hpush
              cases popped with
              | none => simp at hpush
              | some entry =>
                cases entry with
                | Arced tree => simp at hpush
                | Unarced tree =>
                  cases tree with
                  | Leaf leaf => simp at hpush
                  | Node hash left right => simp at hpush
                  | Zero depth => simp at hpush
                  | PackedLeaf leaf =>
                    change (do
                      let (push_status, updated_leaf) ←
                        packed_leaf.PackedLeaf.push
                          ValueInst.tree_hashTreeHashInst
                          ValueInst.corecloneCloneInst leaf value
                      let flow ←
                        core.result.Result.Insts.CoreOpsTry.branch push_status
                      match flow with
                      | core.ops.control_flow.ControlFlow.Continue _ => do
                        let zeros ←
                          core.num.Usize.trailing_zeros next_index
                        let packing_depth ←
                          lift (UScalar.cast .U32 self.packing_depth)
                        let values_to_merge ← lift
                          (core.num.U32.saturating_sub zeros packing_depth)
                        let (status, stack, length) ←
                          builder.Builder.push_loop2 ValueInst
                            { start := 0#u32, «end» := values_to_merge }
                            base_stack self.length
                            (Tree.PackedLeaf updated_leaf)
                        ok (status,
                          { stack := stack, depth := self.depth,
                            level := self.level, length := length,
                            packing_factor := some factor,
                            packing_depth := self.packing_depth,
                            capacity := self.capacity })
                      | core.ops.control_flow.ControlFlow.Break residual => do
                        let status ←
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            Unit (core.convert.FromSame error.Error) residual
                        ok (status,
                          { stack := base_stack, depth := self.depth,
                            level := self.level, length := self.length,
                            packing_factor := some factor,
                            packing_depth := self.packing_depth,
                            capacity := self.capacity })) =
                        ok (core.result.Result.Ok (), result) at hpush
                    cases hleaf_push : packed_leaf.PackedLeaf.push
                        ValueInst.tree_hashTreeHashInst
                        ValueInst.corecloneCloneInst leaf value with
                    | fail error =>
                      rw [hleaf_push] at hpush
                      simp at hpush
                    | div =>
                      rw [hleaf_push] at hpush
                      simp at hpush
                    | ok push_result =>
                      rw [hleaf_push] at hpush
                      simp only [bind_tc_ok] at hpush
                      obtain ⟨push_status, updated_leaf⟩ := push_result
                      cases push_status with
                      | Err error =>
                        simp [core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame] at hpush
                      | Ok success =>
                        cases success
                        simp only [
                          core.result.Result.Insts.CoreOpsTry.branch,
                          lift] at hpush
                        cases hzeros :
                            core.num.Usize.trailing_zeros next_index with
                        | fail error => simp [hzeros] at hpush
                        | div => simp [hzeros] at hpush
                        | ok zeros =>
                          simp only [hzeros, bind_tc_ok] at hpush
                          let values_to_merge :=
                            core.num.U32.saturating_sub zeros
                              (UScalar.cast .U32 self.packing_depth)
                          cases hloop : builder.Builder.push_loop2 ValueInst
                              { start := 0#u32, «end» := values_to_merge }
                              base_stack self.length
                              (Tree.PackedLeaf updated_leaf) with
                          | fail error =>
                            simp [values_to_merge, hloop] at hpush
                          | div => simp [values_to_merge, hloop] at hpush
                          | ok loop_result =>
                            obtain ⟨loop_status, loop_stack, loop_length⟩ :=
                              loop_result
                            simp [values_to_merge, hloop] at hpush
                            obtain ⟨rfl, rfl⟩ := hpush
                            have hlayout : PackingLayout ValueInst
                                (some factor) self.packing_depth := by
                              simpa [hfactor] using
                                (@BuilderInvariant.layout T ValueInst self
                                  hinvariant)
                            have hstack : BuilderStack (some factor) 0
                                self.stack.val self.depth.val
                                self.length.val := by
                              simpa [hfactor, hlevel] using
                                (@BuilderInvariant.stack_dense T ValueInst
                                  self hinvariant)
                            have hmultiple_spec :=
                              core.num.Usize.is_multiple_of.spec self.length
                                factor
                            rw [hmultiple] at hmultiple_spec
                            simp at hmultiple_spec
                            have hunaligned : self.length.val % factor.val ≠
                                0 := hmultiple_spec
                            have hpopped := vec_pop_some_values
                              (A := Global) self.stack base_stack
                              (utils.MaybeArced.Unarced
                                (Tree.PackedLeaf leaf)) hpop
                            have hmember : utils.MaybeArced.Unarced
                                (Tree.PackedLeaf leaf) ∈ self.stack.val := by
                              rw [hpopped]
                              simp
                            obtain ⟨entry_depth, entry_len, hentry_dense⟩ :=
                              hstack.entry_dense hmember
                            cases hentry_dense with
                            | packed packed_factor packed_leaf
                                old_nonempty old_fit =>
                              have hupdated_dense :=
                                packedLeaf_push_preserves_dense ValueInst
                                  hlayout
                                  (DenseTree.packed factor leaf old_nonempty
                                    old_fit)
                                  value hleaf_push
                              have hupdated_fit :=
                                hupdated_dense.length_le_capacity
                              have hold_partial : leaf.values.val.length <
                                  factor.val := by
                                simpa [subtreeCapacity, leafCapacity] using
                                  hupdated_fit
                              obtain ⟨prefix_len, htotal, hprefix_aligned,
                                  hprefix⟩ :=
                                hstack.remove_partial_last hlayout hpopped
                                  (DenseTree.packed factor leaf old_nonempty
                                    old_fit)
                                  old_nonempty (by simpa [subtreeCapacity,
                                    leafCapacity] using hold_partial)
                              have hlength_le := hinvariant.length_le_capacity
                              have hlength_ne : self.length.val ≠
                                  self.capacity.val := by
                                intro heq
                                exact hfull (UScalar.eq_of_val_eq heq)
                              have hcapacity : self.capacity.val =
                                  subtreeCapacity (some factor)
                                    self.depth.val := by
                                simpa [hfactor] using
                                  (@BuilderInvariant.builder_capacity_matches
                                    T ValueInst self hinvariant)
                              have hfits : prefix_len +
                                  (leaf.values.val.length + 1) ≤
                                  subtreeCapacity (some factor)
                                    self.depth.val := by
                                rw [← hcapacity]
                                omega
                              have hnext_value := usize_add_one_value hnext
                              have hloop0 : builder.Builder.push_loop0
                                  ValueInst
                                  { start := 0#u32,
                                    «end» := values_to_merge }
                                  base_stack self.length
                                  (Tree.PackedLeaf updated_leaf) =
                                    ok (core.result.Result.Ok (), loop_stack,
                                      loop_length) := by
                                simpa [push_loop2_eq_loop0] using hloop
                              have hresult : BuilderStack (some factor) 0
                                    loop_stack.val self.depth.val
                                    (self.length.val + 1) ∧
                                  loop_length.val = self.length.val + 1 := by
                                by_cases hupdated_full :
                                    leaf.values.val.length + 1 = factor.val
                                · obtain ⟨count, plan_stack, plan_top,
                                      plan_depth, plan_len, hplan, hcarry,
                                      hcanonical, _⟩ :=
                                    hprefix.append_subtree hlayout
                                      hupdated_dense (by omega)
                                      (by simpa [subtreeCapacity,
                                        leafCapacity] using hprefix_aligned)
                                      hfits
                                  have hnext_cursor : next_index.val =
                                      prefix_len + subtreeCapacity
                                        (some factor) 0 := by
                                    rw [hnext_value, htotal]
                                    simp [subtreeCapacity, leafCapacity]
                                    omega
                                  have hmerge_count : values_to_merge.val =
                                      count :=
                                    push_full_base_merge_count_eq hlayout
                                      hcarry hnext_cursor hzeros
                                  have hpreserved :=
                                    push_loop_preserves_builder_stack hplan
                                      hcanonical values_to_merge hmerge_count
                                      base_stack self.length rfl rfl hloop0
                                  simpa [htotal, Nat.add_assoc] using
                                    hpreserved
                                · have hupdated_partial :
                                      leaf.values.val.length + 1 <
                                        subtreeCapacity (some factor) 0 := by
                                    simp [subtreeCapacity, leafCapacity]
                                    omega
                                  have hcanonical := hprefix.append_partial
                                    hlayout
                                    (top := utils.MaybeArced.Unarced
                                      (Tree.PackedLeaf updated_leaf))
                                    hupdated_dense (by omega)
                                    hupdated_partial
                                    (by simpa [subtreeCapacity,
                                      leafCapacity] using hprefix_aligned)
                                    hfits
                                  have hplan := BuilderMergePlan.done
                                    (ValueInst := ValueInst) base_stack.val
                                    (Tree.PackedLeaf updated_leaf) 0
                                    (leaf.values.val.length + 1)
                                    hupdated_dense (by omega)
                                  have hprefix_factor : prefix_len %
                                      factor.val = 0 := by
                                    simpa [subtreeCapacity, leafCapacity]
                                      using hprefix_aligned
                                  have hupdated_factor_lt :
                                      leaf.values.val.length + 1 <
                                        factor.val := by
                                    simpa [subtreeCapacity, leafCapacity]
                                      using hupdated_partial
                                  have hnext_partial : next_index.val %
                                      factor.val ≠ 0 := by
                                    rw [hnext_value, htotal, Nat.add_assoc,
                                      Nat.add_mod, hprefix_factor, zero_add,
                                      Nat.mod_eq_of_lt hupdated_factor_lt]
                                    rw [Nat.mod_eq_of_lt hupdated_factor_lt]
                                    omega
                                  have hmerge_count : values_to_merge.val =
                                      0 :=
                                    push_partial_base_merge_count_zero
                                      hlayout (by omega) hnext_partial hzeros
                                  have hpreserved :=
                                    push_loop_preserves_builder_stack hplan
                                      hcanonical values_to_merge hmerge_count
                                      base_stack self.length rfl rfl hloop0
                                  simpa [htotal, Nat.add_assoc] using
                                    hpreserved
                              refine ⟨hlayout,
                                @BuilderInvariant.level_valid T ValueInst self
                                  hinvariant,
                                @BuilderInvariant.level_bounded T ValueInst
                                  self hinvariant, hcapacity, ?_, ?_, ?_⟩
                              · simpa [hlevel, hresult.2] using hresult.1
                              · intro hready
                                rcases hready with hlevel_ne | haligned
                                · exact (hlevel_ne hlevel).elim
                                · have hcursor :=
                                    hresult.1.normalized_cursor_of_aligned
                                      hlayout (by simpa [hlevel, hresult.2]
                                        using haligned)
                                  simpa [hlevel, hresult.2] using hcursor
                              · intro _ hpartial_result
                                by_cases hupdated_full :
                                    leaf.values.val.length + 1 = factor.val
                                · exfalso
                                  apply hpartial_result
                                  have hlen_eq : loop_length.val =
                                      prefix_len + factor.val := by
                                    rw [hresult.2, htotal]
                                    omega
                                  have hprefix_factor : prefix_len %
                                      factor.val = 0 := by
                                    simpa [subtreeCapacity, leafCapacity]
                                      using hprefix_aligned
                                  simp [subtreeCapacity, leafCapacity, hlen_eq,
                                    Nat.add_mod, hprefix_factor]
                                · have hupdated_partial :
                                      leaf.values.val.length + 1 <
                                        subtreeCapacity (some factor) 0 := by
                                    simp [subtreeCapacity, leafCapacity]
                                    omega
                                  have hplan := BuilderMergePlan.done
                                    (ValueInst := ValueInst) base_stack.val
                                    (Tree.PackedLeaf updated_leaf) 0
                                    (leaf.values.val.length + 1)
                                    hupdated_dense (by omega)
                                  have hprefix_factor : prefix_len %
                                      factor.val = 0 := by
                                    simpa [subtreeCapacity, leafCapacity]
                                      using hprefix_aligned
                                  have hupdated_factor_lt :
                                      leaf.values.val.length + 1 <
                                        factor.val := by
                                    simpa [subtreeCapacity, leafCapacity]
                                      using hupdated_partial
                                  have hnext_partial : next_index.val %
                                      factor.val ≠ 0 := by
                                    rw [hnext_value, htotal, Nat.add_assoc,
                                      Nat.add_mod, hprefix_factor, zero_add,
                                      Nat.mod_eq_of_lt hupdated_factor_lt]
                                    rw [Nat.mod_eq_of_lt hupdated_factor_lt]
                                    omega
                                  have hmerge_count : values_to_merge.val =
                                      0 :=
                                    push_partial_base_merge_count_zero hlayout
                                      (by omega) hnext_partial hzeros
                                  obtain ⟨hloop_stack, -⟩ :=
                                    push_loop0_follows_merge_plan hplan
                                      { start := 0#u32,
                                        «end» := values_to_merge }
                                      base_stack self.length loop_stack
                                      loop_length (by simp [hmerge_count])
                                      rfl hloop0
                                  exact ⟨base_stack.val,
                                    Tree.PackedLeaf updated_leaf,
                                    leaf.values.val.length + 1, hloop_stack,
                                    hupdated_dense, by omega,
                                    hupdated_partial⟩
          | true =>
            simp only [↓reduceIte] at hpush
            cases hsingle : packed_leaf.PackedLeaf.single
                ValueInst.tree_hashTreeHashInst
                ValueInst.corecloneCloneInst value with
            | fail error => simp [hsingle] at hpush
            | div => simp [hsingle] at hpush
            | ok leaf =>
              simp only [hsingle, bind_tc_ok, lift] at hpush
              cases hzeros : core.num.Usize.trailing_zeros next_index with
              | fail error => simp [hzeros] at hpush
              | div => simp [hzeros] at hpush
              | ok zeros =>
                simp only [hzeros, bind_tc_ok] at hpush
                let values_to_merge := core.num.U32.saturating_sub zeros
                  (UScalar.cast .U32 self.packing_depth)
                cases hloop : builder.Builder.push_loop1 ValueInst
                    { start := 0#u32, «end» := values_to_merge } self.stack
                    self.length (Tree.PackedLeaf leaf) with
                | fail error => simp [values_to_merge, hloop] at hpush
                | div => simp [values_to_merge, hloop] at hpush
                | ok loop_result =>
                  obtain ⟨loop_status, loop_stack, loop_length⟩ := loop_result
                  simp [values_to_merge, hloop] at hpush
                  obtain ⟨rfl, rfl⟩ := hpush
                  have hlayout : PackingLayout ValueInst (some factor)
                      self.packing_depth := by
                    simpa [hfactor] using
                      (@BuilderInvariant.layout T ValueInst self hinvariant)
                  have hstack : BuilderStack (some factor) 0 self.stack.val
                      self.depth.val self.length.val := by
                    simpa [hfactor, hlevel] using
                      (@BuilderInvariant.stack_dense T ValueInst self
                        hinvariant)
                  obtain ⟨produced_leaf, hproduced, hleaf_dense⟩ :=
                    packedLeaf_single_preserves_dense ValueInst hlayout value
                  rw [hsingle] at hproduced
                  cases hproduced
                  have hmultiple_spec :=
                    core.num.Usize.is_multiple_of.spec self.length factor
                  rw [hmultiple] at hmultiple_spec
                  simp at hmultiple_spec
                  have haligned : self.length.val % factor.val = 0 :=
                    hmultiple_spec
                  have hfactor_pos : 0 < factor.val := by
                    simpa [leafCapacity] using hlayout.leafCapacity_pos
                  have hlength_le := hinvariant.length_le_capacity
                  have hlength_ne : self.length.val ≠ self.capacity.val := by
                    intro heq
                    exact hfull (UScalar.eq_of_val_eq heq)
                  have hcapacity : self.capacity.val =
                      subtreeCapacity (some factor) self.depth.val := by
                    simpa [hfactor] using
                      (@BuilderInvariant.builder_capacity_matches T ValueInst
                        self hinvariant)
                  have hfits : self.length.val + 1 ≤
                      subtreeCapacity (some factor) self.depth.val := by
                    rw [← hcapacity]
                    omega
                  have hnext_value := usize_add_one_value hnext
                  have hloop0 : builder.Builder.push_loop0 ValueInst
                      { start := 0#u32, «end» := values_to_merge }
                      self.stack self.length (Tree.PackedLeaf leaf) =
                        ok (core.result.Result.Ok (), loop_stack,
                          loop_length) := by
                    simpa [push_loop1_eq_loop0] using hloop
                  have hresult : BuilderStack (some factor) 0
                        loop_stack.val self.depth.val
                        (self.length.val + 1) ∧
                      loop_length.val = self.length.val + 1 := by
                    by_cases hfactor_one : factor.val = 1
                    · obtain ⟨count, plan_stack, plan_top, plan_depth,
                          plan_len, hplan, hcarry, hcanonical, _⟩ :=
                        hstack.append_subtree hlayout hleaf_dense (by omega)
                          (by simpa [subtreeCapacity, leafCapacity] using
                            haligned) hfits
                      have hnext_cursor : next_index.val = self.length.val +
                          subtreeCapacity (some factor) 0 := by
                        simpa [subtreeCapacity, leafCapacity, hfactor_one]
                          using hnext_value
                      have hmerge_count : values_to_merge.val = count :=
                        push_full_base_merge_count_eq hlayout hcarry
                          hnext_cursor hzeros
                      exact push_loop_preserves_builder_stack hplan hcanonical
                        values_to_merge hmerge_count self.stack self.length rfl
                        rfl hloop0
                    · have htop_partial : 1 < subtreeCapacity
                          (some factor) 0 := by
                        simp [subtreeCapacity, leafCapacity]
                        omega
                      have hfactor_gt : 1 < factor.val := by omega
                      have hcanonical := hstack.append_partial hlayout
                        (top := utils.MaybeArced.Unarced
                          (Tree.PackedLeaf leaf)) hleaf_dense (by omega)
                        htop_partial
                        (by simpa [subtreeCapacity, leafCapacity] using
                          haligned) hfits
                      have hplan := BuilderMergePlan.done
                        (ValueInst := ValueInst) self.stack.val
                        (Tree.PackedLeaf leaf) 0 1 hleaf_dense (by omega)
                      have hnext_partial : next_index.val % factor.val ≠ 0 := by
                        rw [hnext_value, Nat.add_mod, haligned, zero_add,
                          Nat.mod_eq_of_lt hfactor_gt]
                        simpa using hfactor_one
                      have hmerge_count : values_to_merge.val = 0 :=
                        push_partial_base_merge_count_zero hlayout
                          (by omega) hnext_partial hzeros
                      exact push_loop_preserves_builder_stack hplan hcanonical
                        values_to_merge hmerge_count self.stack self.length rfl
                        rfl hloop0
                  refine ⟨hlayout,
                    @BuilderInvariant.level_valid T ValueInst self hinvariant,
                    @BuilderInvariant.level_bounded T ValueInst self
                      hinvariant, hcapacity, ?_, ?_, ?_⟩
                  · simpa [hlevel, hresult.2] using hresult.1
                  · intro hready
                    rcases hready with hlevel_ne | haligned
                    · exact (hlevel_ne hlevel).elim
                    · have hcursor :=
                        hresult.1.normalized_cursor_of_aligned hlayout
                          (by simpa [hlevel, hresult.2] using haligned)
                      simpa [hlevel, hresult.2] using hcursor
                  · intro _ hpartial_result
                    by_cases hfactor_one : factor.val = 1
                    · exfalso
                      apply hpartial_result
                      simpa [subtreeCapacity, leafCapacity, hfactor_one] using
                        Nat.mod_one loop_length.val
                    · have hfactor_gt : 1 < factor.val := by omega
                      have htop_partial : 1 < subtreeCapacity
                          (some factor) 0 := by
                        simp [subtreeCapacity, leafCapacity]
                        omega
                      have hplan := BuilderMergePlan.done
                        (ValueInst := ValueInst) self.stack.val
                        (Tree.PackedLeaf leaf) 0 1 hleaf_dense (by omega)
                      have hnext_partial : next_index.val % factor.val ≠ 0 := by
                        rw [hnext_value, Nat.add_mod, haligned, zero_add,
                          Nat.mod_eq_of_lt hfactor_gt]
                        simpa using hfactor_one
                      have hmerge_count : values_to_merge.val = 0 :=
                        push_partial_base_merge_count_zero hlayout
                          (by omega) hnext_partial hzeros
                      obtain ⟨hloop_stack, -⟩ :=
                        push_loop0_follows_merge_plan hplan
                          { start := 0#u32, «end» := values_to_merge }
                          self.stack self.length loop_stack loop_length
                          (by simp [hmerge_count]) rfl hloop0
                      exact ⟨self.stack.val, Tree.PackedLeaf leaf, 1,
                        hloop_stack, hleaf_dense, by omega, htop_partial⟩

end milhouse.tree
