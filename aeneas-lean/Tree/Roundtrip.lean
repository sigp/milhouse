-- The general roundtrip: `get_recursive` after `with_updated_leaf`, at
-- arbitrary depth, including packed leaves.
import Tree.Lemmas
import Tree.Invariants
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Auxiliary machinery -/

/-- A path-sensitive bound for `with_updated_leaf`.

    The predicate follows the same child at each `Node` as the update.  If it
    reaches a `Zero` subtree for a packable value type, it requires the packed
    sub-index to be at most the computed length of that subtree.  A `Zero`
    subtree has length zero, so this says precisely that a fresh packed leaf is
    created at sub-index zero.  `Zero` nodes in unvisited siblings impose no
    condition.

    This is the local form of the caller invariant `index ≤ length`: deriving
    it from the length of the whole tree additionally requires the usual
    dense-prefix/well-formedness invariant on the tree representation. The
    `True` cases for failed routing operations are harmless here because the
    roundtrip theorem separately assumes that the update succeeded. -/
def updateIndexWithinLength {T : Type} (ValueInst : Value T)
    (self : Tree T) (index depth packing_depth : Std.Usize) : Prop :=
  match self with
  | Tree.Leaf _ => True
  | Tree.PackedLeaf _ => True
  | Tree.Node _ left right =>
    if depth > 0#usize then
      match depth - 1#usize with
      | ok new_depth =>
        match new_depth + packing_depth with
        | ok shift =>
          match index >>> shift with
          | ok shifted =>
            if (shifted &&& 1#usize) = 0#usize then
              updateIndexWithinLength ValueInst left index new_depth
                packing_depth
            else
              updateIndexWithinLength ValueInst right index new_depth
                packing_depth
          | _ => True
        | _ => True
      | _ => True
    else True
  | Tree.Zero _ =>
    ∀ factor, utils.opt_packing_factor ValueInst.tree_hashTreeHashInst =
        ok (some factor) →
      ∃ sub len, index % factor = ok sub ∧
        Tree.compute_len ValueInst self = ok len ∧ sub.val ≤ len.val

/-- Induction measure tie-breaker: a `Zero` node first rewrites itself to a
    `Node` at the *same* depth before recursing, so it costs one extra tick. -/
private def zbit {T : Type} : Tree T → Nat
  | Tree.Zero _ => 1
  | _ => 0

private theorem zbit_le_one {T : Type} (t : Tree T) : zbit t ≤ 1 := by
  cases t <;> simp [zbit]

/-- At a `Zero` subtree, the length-based bound is equivalent to alignment at
    packed sub-index zero. -/
private theorem updateIndexWithinLength_zero_iff {T : Type}
    (ValueInst : Value T) (d index depth packing_depth : Std.Usize) :
    updateIndexWithinLength ValueInst (Tree.Zero d) index depth packing_depth ↔
      ∀ factor, utils.opt_packing_factor ValueInst.tree_hashTreeHashInst =
        ok (some factor) → index % factor = ok 0#usize := by
  constructor
  · intro h factor hf
    obtain ⟨sub, len, hsub, hlen, hle⟩ := h factor hf
    simp [Tree.compute_len] at hlen
    subst len
    have hsub0 : sub = 0#usize := by scalar_tac
    simpa [hsub0] using hsub
  · intro h factor hf
    exact ⟨0#usize, 0#usize, h factor hf, by simp [Tree.compute_len], by simp⟩

/-- Expanding a `Zero` into a node with two `Zero` children preserves the
    path-sensitive length bound. -/
private theorem updateIndexWithinLength_node_zeros {T : Type}
    (ValueInst : Value T) (rl : lock_api.rwlock.RwLock
      parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize))
    (d index depth packing_depth : Std.Usize)
    (halign : ∀ factor,
      utils.opt_packing_factor ValueInst.tree_hashTreeHashInst =
        ok (some factor) → index % factor = ok 0#usize) :
    updateIndexWithinLength ValueInst
      (Tree.Node rl (Tree.Zero d) (Tree.Zero d)) index depth packing_depth := by
  unfold updateIndexWithinLength
  split
  · cases hnd : depth - 1#usize with
    | fail e => simp
    | div => simp
    | ok new_depth =>
      simp
      cases hshift : new_depth + packing_depth with
      | fail e => simp
      | div => simp
      | ok shift =>
        simp
        cases hshr : index >>> shift with
        | fail e => simp
        | div => simp
        | ok shifted =>
          simp
          exact (updateIndexWithinLength_zero_iff ValueInst _ _ _ _).2
            halign
  · trivial

/-- For a non-packable type the path-sensitive bound is vacuous. -/
private theorem updateIndexWithinLength_of_nonpackable {T : Type}
    (ValueInst : Value T)
    (hpf : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok none)
    (self : Tree T) (index depth packing_depth : Std.Usize) :
    updateIndexWithinLength ValueInst self index depth packing_depth := by
  induction self generalizing depth with
  | Leaf l => trivial
  | PackedLeaf pl => trivial
  | Zero d =>
    intro factor hf
    rw [hpf] at hf
    simp at hf
  | Node rl left right ihl ihr =>
    unfold updateIndexWithinLength
    split
    · cases hnd : depth - 1#usize with
      | fail e => simp
      | div => simp
      | ok new_depth =>
        simp
        cases hshift : new_depth + packing_depth with
        | fail e => simp
        | div => simp
        | ok shift =>
          simp
          cases hshr : index >>> shift with
          | fail e => simp
          | div => simp
          | ok shifted =>
            simp
            split
            · exact ihl new_depth
            · exact ihr new_depth
    · trivial

/-- Inversion for `Result` bind. -/
private theorem bind_eq_ok_iff {α β : Type} {x : Result α}
    {f : α → Result β} {y : β} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Inversion for `Vec.push`. -/
private theorem push_eq_ok {α : Type} {v : alloc.vec.Vec α} {x : α}
    {v' : alloc.vec.Vec α} (h : alloc.vec.Vec.push v x = ok v') :
    v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  grind

/-- If `opt_packing_factor` returns `some factor`, the underlying trait
    method returns `factor`. -/
private theorem opt_packing_factor_some {T : Type}
    {thi : tree_hash.TreeHash T} {factor : Std.Usize}
    (h : utils.opt_packing_factor thi = ok (some factor)) :
    thi.tree_hash_packing_factor = ok factor := by
  unfold utils.opt_packing_factor at h
  cases htht : thi.tree_hash_type with
  | fail e => rw [htht] at h; simp at h
  | div => rw [htht] at h; simp at h
  | ok tht =>
    rw [htht] at h
    cases tht <;> simp at h
    cases hfac : thi.tree_hash_packing_factor with
    | fail e => rw [hfac] at h; simp at h
    | div => rw [hfac] at h; simp at h
    | ok i => rw [hfac] at h; simp at h; simp [h]

/-! ## Packed-leaf lemmas -/

/-- After a successful `insert_mut` at `sub`, the values contain the new
    value at `sub`. -/
private theorem insert_mut_ok {T : Type} {thi : tree_hash.TreeHash T}
    {cl : core.clone.Clone T} {lf : packed_leaf.PackedLeaf T}
    {sub : Std.Usize} {v : T} {updated : packed_leaf.PackedLeaf T}
    (h : packed_leaf.PackedLeaf.insert_mut thi cl lf sub v =
      ok (core.result.Result.Ok (), updated)) :
    updated.values[sub.val]? = some v := by
  unfold packed_leaf.PackedLeaf.insert_mut at h
  simp [lock_api.rwlock.RwLock.get_mut,
    alloy_primitives.bits.fixed.FixedBytes.ZERO] at h
  split at h
  · -- `sub = len`: push
    next heq =>
    cases hp : alloc.vec.Vec.push lf.values v with
    | fail e => rw [hp] at h; simp at h
    | div => rw [hp] at h; simp at h
    | ok v' =>
      rw [hp] at h
      simp at h
      subst h
      have hv' := push_eq_ok hp
      subst heq
      simp [hv']
  · -- `sub < len`: set in place, or out of bounds
    split at h
    · next hlt =>
      cases him : alloc.vec.Vec.index_mut_usize lf.values sub with
      | fail e => rw [him] at h; simp at h
      | div => rw [him] at h; simp at h
      | ok p =>
        rw [him] at h
        obtain ⟨elem, back⟩ := p
        simp at h
        -- characterize `back`
        unfold alloc.vec.Vec.index_mut_usize at him
        split at him <;>
          simp only [ok.injEq, Prod.mk.injEq, reduceCtorEq] at him
        obtain ⟨-, hback⟩ := him
        subst hback
        subst h
        simp [hlt]
    · simp at h

/-- After a successful `insert_at_index`, the packing factor and sub-index
    computations succeeded and the new value sits at the sub-index. -/
private theorem insert_at_index_ok {T : Type} {thi : tree_hash.TreeHash T}
    {cl : core.clone.Clone T} {pl val : packed_leaf.PackedLeaf T}
    {index : Std.Usize} {v : T}
    (h : packed_leaf.PackedLeaf.insert_at_index thi cl pl index v =
      ok (core.result.Result.Ok val)) :
    ∃ factor sub, thi.tree_hash_packing_factor = ok factor ∧
      index % factor = ok sub ∧ val.values[sub.val]? = some v := by
  unfold packed_leaf.PackedLeaf.insert_at_index at h
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cv, hcv, factor, hf, sub, hs, ⟨r, upd⟩, hins, h⟩ := h
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
  | Ok u =>
    cases u
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    subst h
    exact ⟨factor, sub, hf, hs, insert_mut_ok hins⟩

/-- `get_recursive` on a packed leaf at depth 0, given the packing
    computations and the value at the sub-index. -/
private theorem get_recursive_packed {T : Type} (ValueInst : Value T)
    {pl : packed_leaf.PackedLeaf T} {index : Std.Usize} {v : T}
    {factor sub : Std.Usize} (packing_depth : Std.Usize)
    (hf : ValueInst.tree_hashTreeHashInst.tree_hash_packing_factor =
      ok factor)
    (hs : index % factor = ok sub)
    (hg : pl.values[sub.val]? = some v) :
    Tree.get_recursive ValueInst (Tree.PackedLeaf pl) index 0#usize
      packing_depth = ok (some v) := by
  unfold Tree.get_recursive
  simp [hf, hs, core.slice.Slice.get, alloc.vec.Vec.deref]
  simpa using hg

/-- Trees containing no `PackedLeaf` node (used by the restricted
    corollary below). -/
inductive NoPacked {T : Type} : Tree T → Prop
  | leaf (l : leaf.Leaf T) : NoPacked (Tree.Leaf l)
  | node (rl : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (left right : triomphe.arc.Arc (Tree T)) :
      NoPacked left → NoPacked right → NoPacked (Tree.Node rl left right)
  | zero (d : Std.Usize) : NoPacked (Tree.Zero d)

/-- For a non-packable value type, the packing depth is `none`. -/
private theorem opt_packing_depth_none {T : Type}
    (thi : tree_hash.TreeHash T)
    (hpf : utils.opt_packing_factor thi = ok none) :
    utils.opt_packing_depth thi = ok none := by
  unfold utils.opt_packing_depth
  simp [hpf, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

/-! ## Leaf and packed-leaf base cases of the induction -/

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

private theorem update_on_packed {T : Type} {ValueInst : Value T}
    {pl : packed_leaf.PackedLeaf T} {index depth : Std.Usize} {new_value : T}
    {t : Tree T}
    (h : Tree.with_updated_leaf ValueInst (Tree.PackedLeaf pl) index new_value
      depth = ok (core.result.Result.Ok t))
    (packing_depth : Std.Usize) :
    Tree.get_recursive ValueInst t index depth packing_depth =
      ok (some new_value) := by
  unfold Tree.with_updated_leaf at h
  split at h
  · next hdep =>
    subst hdep
    simp [triomphe.arc.Arc.new] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hins, h⟩ := h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
    | Ok val =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      subst h
      obtain ⟨factor, sub, hf, hs, hg⟩ := insert_at_index_ok hins
      exact get_recursive_packed ValueInst packing_depth hf hs hg
  · simp at h

/-! ## The main induction -/

private theorem get_after_update_aux {T : Type} (ValueInst : Value T)
    {opd : Option Std.Usize}
    (hpd : utils.opt_packing_depth ValueInst.tree_hashTreeHashInst = ok opd)
    (index : Std.Usize) (new_value : T) :
    ∀ (n : Nat) (depth : Std.Usize) (self t : Tree T),
      2 * depth.val + zbit self ≤ n →
      updateIndexWithinLength ValueInst self index depth
        (core.option.Option.unwrap_or opd 0#usize) →
      Tree.with_updated_leaf ValueInst self index new_value depth =
        ok (core.result.Result.Ok t) →
      Tree.get_recursive ValueInst t index depth
        (core.option.Option.unwrap_or opd 0#usize) = ok (some new_value) := by
  intro n
  induction n with
  | zero =>
    intro depth self t hn hindex h
    cases self with
    | Leaf l => exact update_on_leaf h _
    | PackedLeaf pl => exact update_on_packed h _
    | Node rl left right =>
      -- `2 * depth.val ≤ 0` forces `depth = 0`, so the `depth > 0` guard
      -- fails and the update returns an error: contradiction.
      unfold Tree.with_updated_leaf at h
      simp only [zbit] at hn
      split at h
      · next hgt =>
        have : 0 < depth.val := by scalar_tac
        omega
      · simp at h
    | Zero d => simp [zbit] at hn
  | succ n ih =>
    intro depth self t hn hindex h
    cases self with
    | Leaf l => exact update_on_leaf h _
    | PackedLeaf pl => exact update_on_packed h _
    | Node rl left right =>
      simp only [zbit] at hn
      unfold Tree.with_updated_leaf at h
      split at h
      case isFalse => simp at h
      case isTrue hgt =>
      rw [hpd] at h
      simp [lift,
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
            simp only [hnd, hi, hi1, lift, bind_tc_ok,
              triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
            rw [if_pos hbit]
            exact ih nd left val
              (by have := zbit_le_one left; omega)
              (by
                unfold updateIndexWithinLength at hindex
                simp only [if_pos hgt, hnd, hi, hi1, if_pos hbit] at hindex
                exact hindex)
              hrec
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
            simp only [hnd, hi, hi1, lift, bind_tc_ok,
              triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
            rw [if_neg hbit]
            exact ih nd right val
              (by have := zbit_le_one right; omega)
              (by
                unfold updateIndexWithinLength at hindex
                simp only [if_pos hgt, hnd, hi, hi1, if_neg hbit] at hindex
                exact hindex)
              hrec
    | Zero d =>
      simp only [zbit] at hn
      unfold Tree.with_updated_leaf at h
      split at h
      case isFalse => simp at h
      case isTrue hdeq =>
      split at h
      case isTrue hdep =>
        -- depth 0: a fresh leaf (unpacked) or a fresh single-element packed
        -- leaf (packed) is created.
        subst hdep
        cases hfac : utils.opt_packing_factor
            ValueInst.tree_hashTreeHashInst with
        | fail e => rw [hfac] at h; simp at h
        | div => rw [hfac] at h; simp at h
        | ok o =>
        rw [hfac] at h
        cases o with
        | none =>
          simp [core.option.Option.is_some, Tree.leaf, leaf.Leaf.new,
            leaf.Leaf.with_hash, alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at h
          subst h
          simpa using get_recursive_leaf ValueInst _ index _
        | some f =>
          have hf := opt_packing_factor_some hfac
          have hsub0 :=
            (updateIndexWithinLength_zero_iff ValueInst d index 0#usize
              (core.option.Option.unwrap_or opd 0#usize)).1 hindex f hfac
          simp only [core.option.Option.is_some] at h
          unfold packed_leaf.PackedLeaf.single at h
          rw [hf] at h
          simp [alloc.vec.Vec.with_capacity,
            alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨v1, hp, h⟩ := h
          simp at h
          subst h
          have hv1 := push_eq_ok hp
          apply get_recursive_packed ValueInst _ hf hsub0
          simp [hv1]
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
        have halign :=
          (updateIndexWithinLength_zero_iff ValueInst d index depth
            (core.option.Option.unwrap_or opd 0#usize)).1 hindex
        exact ih depth _ t (by simp only [zbit]; omega)
          (updateIndexWithinLength_node_zeros ValueInst _ i index depth
            (core.option.Option.unwrap_or opd 0#usize) halign)
          h

/-! ## The theorems -/

/-- **General roundtrip at arbitrary depth, packed leaves included.** If
    `with_updated_leaf` succeeds at `index`/`depth`, then `get_recursive` at
    the same `index`/`depth` on the updated tree returns the new value.

    The packing depth passed to `get_recursive` is
    `opt_packing_depth().unwrap_or(0)`, matching milhouse's callers.

    The one side condition (`hindex`) follows the update path and bounds the
    packed sub-index by the length of a selected `Zero` subtree. Since that
    length is zero, a fresh `PackedLeaf::single` is read back at sub-index zero.
    Zeros in unvisited siblings impose no condition. A caller-level theorem can
    derive this local bound from `DenseTree` and `index ≤ length`; that bridge
    lemma is tracked in `Tree/INVARIANTS_TODO.md`. -/
theorem get_recursive_with_updated_leaf_general {T : Type}
    (ValueInst : Value T) {opd : Option Std.Usize}
    (hpd : utils.opt_packing_depth ValueInst.tree_hashTreeHashInst = ok opd)
    {self t : Tree T} {index depth : Std.Usize} {new_value : T}
    (hindex : updateIndexWithinLength ValueInst self index depth
      (core.option.Option.unwrap_or opd 0#usize))
    (h : Tree.with_updated_leaf ValueInst self index new_value depth =
      ok (core.result.Result.Ok t)) :
    Tree.get_recursive ValueInst t index depth
      (core.option.Option.unwrap_or opd 0#usize) = ok (some new_value) :=
  get_after_update_aux ValueInst hpd index new_value
    (2 * depth.val + zbit self) depth self t (Nat.le_refl _) hindex h

/-- The earlier restricted roundtrip, now a corollary: for a non-packable
    value type the length side condition is vacuous (and `NoPacked` is not
    needed at all). -/
theorem get_recursive_with_updated_leaf {T : Type} (ValueInst : Value T)
    (hpf : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok none)
    {self t : Tree T} {index depth : Std.Usize} {new_value : T}
    (hnp : NoPacked self)
    (h : Tree.with_updated_leaf ValueInst self index new_value depth =
      ok (core.result.Result.Ok t)) :
    Tree.get_recursive ValueInst t index depth 0#usize =
      ok (some new_value) := by
  have hpd := opt_packing_depth_none _ hpf
  have hgen := get_recursive_with_updated_leaf_general ValueInst hpd
    (updateIndexWithinLength_of_nonpackable ValueInst hpf self index depth
      0#usize) h
  simpa using hgen

end milhouse.tree
