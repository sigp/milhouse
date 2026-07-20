-- The general roundtrip: `get_recursive` after `with_updated_leaf`, at
-- arbitrary depth.
import Tree.Lemmas
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Auxiliary machinery -/

/-- Trees containing no `PackedLeaf` node. Packed leaves only arise for
    "basic" (packable) value types; the roundtrip theorem is stated for
    non-packable types (`opt_packing_factor = none`), whose trees are
    unpacked. -/
inductive NoPacked {T : Type} : Tree T → Prop
  | leaf (l : leaf.Leaf T) : NoPacked (Tree.Leaf l)
  | node (rl : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (left right : triomphe.arc.Arc (Tree T)) :
      NoPacked left → NoPacked right → NoPacked (Tree.Node rl left right)
  | zero (d : Std.Usize) : NoPacked (Tree.Zero d)

/-- Induction measure tie-breaker: a `Zero` node first rewrites itself to a
    `Node` at the *same* depth before recursing, so it costs one extra tick. -/
private def zbit {T : Type} : Tree T → Nat
  | Tree.Zero _ => 1
  | _ => 0

private theorem zbit_le_one {T : Type} (t : Tree T) : zbit t ≤ 1 := by
  cases t <;> simp [zbit]

/-- Inversion for `Result` bind. -/
private theorem bind_eq_ok_iff {α β : Type} {x : Result α}
    {f : α → Result β} {y : β} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- For a non-packable value type, the packing depth is `none`. -/
private theorem opt_packing_depth_none {T : Type}
    (thi : tree_hash.TreeHash T)
    (hpf : utils.opt_packing_factor thi = ok none) :
    utils.opt_packing_depth thi = ok none := by
  unfold utils.opt_packing_depth
  simp [hpf, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

/-! ## The Leaf base case -/

private theorem update_on_leaf {T : Type} {ValueInst : Value T}
    {l : leaf.Leaf T} {index depth : Std.Usize} {new_value : T} {t : Tree T}
    (h : Tree.with_updated_leaf ValueInst (Tree.Leaf l) index new_value depth
       = ok (core.result.Result.Ok t))
    (packing_depth : Std.Usize) :
    Tree.get_recursive ValueInst t index depth packing_depth =
      ok (some new_value) := by
  unfold Tree.with_updated_leaf at h
  split at h
  · next hdep =>
    subst hdep
    simp [Tree.leaf, leaf.Leaf.new, leaf.Leaf.with_hash,
      alloy_primitives.bits.fixed.FixedBytes.ZERO,
      lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at h
    subst h
    simpa using get_recursive_leaf ValueInst _ index packing_depth
  · simp at h

/-! ## The main induction -/

private theorem get_after_update_aux {T : Type} (ValueInst : Value T)
    (hpf : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok none)
    (index : Std.Usize) (new_value : T) :
    ∀ (n : Nat) (depth : Std.Usize) (self t : Tree T),
      2 * depth.val + zbit self ≤ n →
      NoPacked self →
      Tree.with_updated_leaf ValueInst self index new_value depth =
        ok (core.result.Result.Ok t) →
      Tree.get_recursive ValueInst t index depth 0#usize =
        ok (some new_value) := by
  have hpd := opt_packing_depth_none _ hpf
  intro n
  induction n with
  | zero =>
    intro depth self t hn hnp h
    cases hnp with
    | leaf l => exact update_on_leaf h 0#usize
    | node rl left right hl hr =>
      -- `2 * depth.val ≤ 0` forces `depth = 0`, so the `depth > 0` guard
      -- fails and the update returns an error: contradiction.
      unfold Tree.with_updated_leaf at h
      simp only [zbit] at hn
      split at h
      · next hgt =>
        have : 0 < depth.val := by scalar_tac
        omega
      · simp at h
    | zero d => simp [zbit] at hn
  | succ n ih =>
    intro depth self t hn hnp h
    cases hnp with
    | leaf l => exact update_on_leaf h 0#usize
    | node rl left right hl hr =>
      simp only [zbit] at hn
      unfold Tree.with_updated_leaf at h
      split at h
      case isFalse => simp at h
      case isTrue hgt =>
      rw [hpd] at h
      simp [lift, core.option.Option.unwrap_or_none,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone,
        alloy_primitives.bits.fixed.FixedBytes.ZERO,
        lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new, Tree.node] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨nd, hnd, i, hi, i1, hi1, h⟩ := h
      -- relate `nd.val` to `depth.val`
      have hsub := UScalar.sub_equiv depth 1#usize
      rw [hnd] at hsub
      have hndval : depth.val = nd.val + 1 := by
        obtain ⟨-, h1, -⟩ := hsub; scalar_tac
      -- the bit test
      split at h
      case isTrue hbit =>
        -- update descended left
        cases hrec : Tree.with_updated_leaf ValueInst left index new_value nd
          with
        | fail e => rw [hrec] at h; simp at h
        | div => rw [hrec] at h; simp at h
        | ok r =>
          rw [hrec] at h
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at h
          | Ok val =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at h
            subst h
            unfold Tree.get_recursive
            rw [if_pos hgt]
            simp [hnd, hi, hi1, hbit, lift,
              triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
            exact ih nd left val
              (by have := zbit_le_one left; omega) hl hrec
      case isFalse hbit =>
        -- update descended right
        cases hrec : Tree.with_updated_leaf ValueInst right index new_value nd
          with
        | fail e => rw [hrec] at h; simp at h
        | div => rw [hrec] at h; simp at h
        | ok r =>
          rw [hrec] at h
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at h
          | Ok val =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at h
            subst h
            unfold Tree.get_recursive
            rw [if_pos hgt]
            simp [hnd, hi, hi1, hbit, lift,
              triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
            exact ih nd right val
              (by have := zbit_le_one right; omega) hr hrec
    | zero d =>
      simp only [zbit] at hn
      unfold Tree.with_updated_leaf at h
      split at h
      case isFalse => simp at h
      case isTrue hdeq =>
      split at h
      case isTrue hdep =>
        -- depth 0: a fresh leaf is created (no packing for this type)
        subst hdep
        rw [hpf] at h
        simp [core.option.Option.is_some, Tree.leaf, leaf.Leaf.new,
          leaf.Leaf.with_hash, alloy_primitives.bits.fixed.FixedBytes.ZERO,
          lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at h
        subst h
        simpa using get_recursive_leaf ValueInst _ index 0#usize
      case isFalse hdep =>
        -- depth > 0: the Zero node rewrites itself into a Node of two Zero
        -- children and recurses at the same depth, one measure tick lower.
        simp [Tree.zero, triomphe.arc.Arc.new,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          alloy_primitives.bits.fixed.FixedBytes.ZERO, Tree.node,
          lock_api.rwlock.RwLock.new,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i, hi, h⟩ := h
        exact ih depth _ t (by simp only [zbit]; omega)
          (NoPacked.node _ _ _ (NoPacked.zero i) (NoPacked.zero i)) h

/-! ## The theorem -/

/-- **General roundtrip at arbitrary depth.** For a non-packable value type,
    if `with_updated_leaf` succeeds at `index`/`depth` on a tree without
    packed leaves, then `get_recursive` at the same `index`/`depth` on the
    updated tree returns the new value.

    The packing depth passed to `get_recursive` is `0`, matching what
    milhouse's callers compute via `opt_packing_depth().unwrap_or(0)` for a
    non-packable type. -/
theorem get_recursive_with_updated_leaf {T : Type} (ValueInst : Value T)
    (hpf : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok none)
    {self t : Tree T} {index depth : Std.Usize} {new_value : T}
    (hnp : NoPacked self)
    (h : Tree.with_updated_leaf ValueInst self index new_value depth =
      ok (core.result.Result.Ok t)) :
    Tree.get_recursive ValueInst t index depth 0#usize =
      ok (some new_value) :=
  get_after_update_aux ValueInst hpf index new_value
    (2 * depth.val + zbit self) depth self t (Nat.le_refl _) hnp h

end milhouse.tree
