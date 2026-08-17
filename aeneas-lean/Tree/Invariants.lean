-- Structural invariants for milhouse trees.
import Tree.Funs
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open milhouse

namespace milhouse.tree

/-! ## Packing configuration -/

/-- The relationship between the packing operations supplied by `Value T` and
    the layout used by a tree.

    `PackingLayout` deliberately includes the power-of-two law.  The extracted
    trait signatures permit arbitrary packing factors, while tree routing uses
    `packing_depth` bits and therefore relies on
    `packing_factor = 2 ^ packing_depth`. -/
inductive PackingLayout {T : Type} (ValueInst : Value T) :
    Option Std.Usize → Std.Usize → Prop where
  | unpacked
      (factor_eq : utils.opt_packing_factor
        ValueInst.tree_hashTreeHashInst = ok none)
      (depth_eq : utils.opt_packing_depth
        ValueInst.tree_hashTreeHashInst = ok none) :
      PackingLayout ValueInst none 0#usize
  | packed (factor packing_depth : Std.Usize)
      (factor_eq : utils.opt_packing_factor
        ValueInst.tree_hashTreeHashInst = ok (some factor))
      (depth_eq : utils.opt_packing_depth
        ValueInst.tree_hashTreeHashInst = ok (some packing_depth))
      (factor_is_power : factor.val = 2 ^ packing_depth.val) :
      PackingLayout ValueInst (some factor) packing_depth

/-! ## Dense tree shape -/

/-- Capacity of one materialized leaf position. An unpacked leaf contains one
    value; a packed leaf contains up to `factor` values. -/
def leafCapacity : Option Std.Usize → Nat
  | none => 1
  | some factor => factor.val

/-- Capacity represented by a subtree at the given tree depth. The depth here
    excludes the packing depth, matching `Tree.get_recursive` and the cached
    depth in `ListInner`/`VectorInner`. -/
def subtreeCapacity (packing_factor : Option Std.Usize) (depth : Nat) : Nat :=
  leafCapacity packing_factor * 2 ^ depth

/-- Resulting logical length of a successful dense update at a subtree. The
    update grows only at the current right edge and only when spare capacity
    remains; a full subtree wraps routing and therefore stays full. -/
def updatedDenseLength (packing_factor : Option Std.Usize) (depth : Nat)
    (index : Std.Usize) (len : Nat) : Nat :=
  if index.val % subtreeCapacity packing_factor depth = len ∧
      len < subtreeCapacity packing_factor depth
  then len + 1
  else len

/-- Domain condition for applying several pending updates to a dense backing
    tree. Existing indices may be updated sparsely, but any extension must be
    a complete interval from the old right edge and no update may occur beyond
    the reported new length. -/
structure DenseUpdateDomain (old_len new_len : Nat)
    (has_update : Nat → Prop) : Prop where
  length_mono : old_len ≤ new_len
  extension_complete : ∀ index,
    old_len ≤ index → index < new_len → has_update index
  updates_bounded : ∀ index, has_update index → index < new_len

/-- A map containing replacements only is dense-domain valid. -/
theorem DenseUpdateDomain.replacements {old_len : Nat}
    {has_update : Nat → Prop}
    (hbounded : ∀ index, has_update index → index < old_len) :
    DenseUpdateDomain old_len old_len has_update := by
  exact ⟨Nat.le_refl _, by omega, hbounded⟩

/-- A singleton update at the old right edge describes a one-element dense
    extension. -/
theorem DenseUpdateDomain.singleton_extension (old_len : Nat) :
    DenseUpdateDomain old_len (old_len + 1) (fun index => index = old_len) := by
  constructor <;> omega

/-- A tree containing exactly `len` materialized values as a dense left prefix
    of a subtree at `depth`.

    The indices use `Nat` because depth and length are ghost state. Bridge
    lemmas relate them to the `.val` fields of translated `Usize` values.

    The `node` rule is the key left-density condition: the left child is
    non-empty, and a non-empty right child is permitted only after the left
    child reaches its full capacity. Applied recursively, this means that no
    materialized value occurs after a `Zero` padding region. Hash-cache fields
    are intentionally ignored. -/
inductive DenseTree {T : Type} :
    Option Std.Usize → Tree T → Nat → Nat → Prop where
  | zero (packing_factor : Option Std.Usize) (depth : Std.Usize) :
      DenseTree packing_factor (Tree.Zero depth) depth.val 0
  | leaf (l : leaf.Leaf T) :
      DenseTree none (Tree.Leaf l) 0 1
  | packed (factor : Std.Usize) (pl : packed_leaf.PackedLeaf T)
      (values_nonempty : 0 < pl.values.val.length)
      (values_fit : pl.values.val.length ≤ factor.val) :
      DenseTree (some factor) (Tree.PackedLeaf pl) 0 pl.values.val.length
  | node (packing_factor : Option Std.Usize)
      (rl : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (left right : triomphe.arc.Arc (Tree T))
      (child_depth left_len right_len : Nat)
      (left_dense : DenseTree packing_factor left child_depth left_len)
      (right_dense : DenseTree packing_factor right child_depth right_len)
      (left_nonempty : 0 < left_len)
      (left_full_before_right :
        0 < right_len →
          left_len = subtreeCapacity packing_factor child_depth) :
      DenseTree packing_factor (Tree.Node rl left right) (child_depth + 1)
        (left_len + right_len)

/-- Internal input shape used while proving `with_updated_leaf`: the function
    transiently expands a `Zero` into a node with two zero children before it
    recurses. Such an all-empty node is not a canonical `DenseTree`, but every
    recursive child still is. -/
private inductive UpdateReady {T : Type} :
    Option Std.Usize → Tree T → Nat → Nat → Prop where
  | zero (packing_factor : Option Std.Usize) (depth : Std.Usize) :
      UpdateReady packing_factor (Tree.Zero depth) depth.val 0
  | leaf (l : leaf.Leaf T) :
      UpdateReady none (Tree.Leaf l) 0 1
  | packed (factor : Std.Usize) (pl : packed_leaf.PackedLeaf T)
      (values_nonempty : 0 < pl.values.val.length)
      (values_fit : pl.values.val.length ≤ factor.val) :
      UpdateReady (some factor) (Tree.PackedLeaf pl) 0 pl.values.val.length
  | node (packing_factor : Option Std.Usize)
      (rl : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (left right : triomphe.arc.Arc (Tree T))
      (child_depth left_len right_len : Nat)
      (left_dense : DenseTree packing_factor left child_depth left_len)
      (right_dense : DenseTree packing_factor right child_depth right_len)
      (shape :
        (left_len = 0 ∧ right_len = 0) ∨
        (0 < left_len ∧ (0 < right_len →
          left_len = subtreeCapacity packing_factor child_depth))) :
      UpdateReady packing_factor (Tree.Node rl left right) (child_depth + 1)
        (left_len + right_len)

private theorem UpdateReady.ofDense {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T} {depth len : Nat}
    (h : DenseTree packing_factor tree depth len) :
    UpdateReady packing_factor tree depth len := by
  cases h with
  | zero packing_factor depth => exact UpdateReady.zero packing_factor depth
  | leaf l => exact UpdateReady.leaf l
  | packed factor pl hpos hfit => exact UpdateReady.packed factor pl hpos hfit
  | node packing_factor rl left right child_depth left_len right_len
      hleft hright hleftpos hfull =>
    exact UpdateReady.node packing_factor rl left right child_depth left_len
      right_len hleft hright (Or.inr ⟨hleftpos, hfull⟩)

/-- The path-sensitive bound consumed by the update/read roundtrip theorem.

    At a selected `Zero`, it rules out creating a packed leaf at a nonzero
    sub-index. `DenseTree.updateIndexWithinLength` below derives this local
    condition from the global dense-prefix length bound. -/
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

/-! ## Basic consequences -/

/-- A valid packing layout always has a positive leaf capacity. -/
theorem PackingLayout.leafCapacity_pos {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (h : PackingLayout ValueInst packing_factor packing_depth) :
    0 < leafCapacity packing_factor := by
  cases h with
  | unpacked => simp [leafCapacity]
  | packed factor packing_depth _ _ hpower =>
    simp [leafCapacity, hpower]

/-- Every subtree capacity described by a valid layout is positive. -/
theorem PackingLayout.subtreeCapacity_pos {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (h : PackingLayout ValueInst packing_factor packing_depth)
    (depth : Nat) :
    0 < subtreeCapacity packing_factor depth := by
  have hleaf := h.leafCapacity_pos
  simp [subtreeCapacity, hleaf]

/-- Under a valid layout, subtree capacity is exactly the power of two used
    by the translated bit routing. -/
theorem PackingLayout.subtreeCapacity_eq_two_pow {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (h : PackingLayout ValueInst packing_factor packing_depth)
    (depth : Nat) :
    subtreeCapacity packing_factor depth =
      2 ^ (packing_depth.val + depth) := by
  cases h with
  | unpacked => simp [subtreeCapacity, leafCapacity]
  | packed factor packing_depth _ _ hpower =>
    simp [subtreeCapacity, leafCapacity, hpower, pow_add]

/-- The optional packing-depth query recorded by a layout. -/
theorem PackingLayout.opt_packing_depth_eq {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (h : PackingLayout ValueInst packing_factor packing_depth) :
    utils.opt_packing_depth ValueInst.tree_hashTreeHashInst =
      ok (if packing_factor.isSome then some packing_depth else none) := by
  cases h with
  | unpacked factor_eq depth_eq => simpa using depth_eq
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    simpa using depth_eq

/-- The optional packing-factor query recorded by a layout. -/
theorem PackingLayout.opt_packing_factor_eq {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (h : PackingLayout ValueInst packing_factor packing_depth) :
    utils.opt_packing_factor ValueInst.tree_hashTreeHashInst =
      ok packing_factor := by
  cases h with
  | unpacked factor_eq depth_eq => exact factor_eq
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    exact factor_eq

/-- Unwrapping the optional depth recorded by a layout yields its routing
    depth in both packed and unpacked modes. -/
theorem PackingLayout.unwrap_opt_packing_depth_eq {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (h : PackingLayout ValueInst packing_factor packing_depth) :
    core.option.Option.unwrap_or
        (if packing_factor.isSome then some packing_depth else none)
        0#usize = packing_depth := by
  cases h <;> simp [core.option.Option.unwrap_or]

/-- If the optional packing-factor query succeeds with `some factor`, the
    underlying trait method returned that factor. -/
theorem tree_hash_packing_factor_eq_of_opt_some {T : Type}
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
    cases hfactor : thi.tree_hash_packing_factor with
    | fail e => rw [hfactor] at h; simp at h
    | div => rw [hfactor] at h; simp at h
    | ok actual =>
      rw [hfactor] at h
      simp at h
      exact congrArg ok h

/-- A packed layout exposes its packing factor through the raw trait method
    used by `PackedLeaf.single` and tree updates. -/
theorem PackingLayout.tree_hash_packing_factor_eq {T : Type}
    {ValueInst : Value T} {factor packing_depth : Std.Usize}
    (h : PackingLayout ValueInst (some factor) packing_depth) :
    ValueInst.tree_hashTreeHashInst.tree_hash_packing_factor = ok factor := by
  cases h with
  | packed factor packing_depth factor_eq depth_eq factor_is_power =>
    exact tree_hash_packing_factor_eq_of_opt_some factor_eq

/-- The logical length of a dense tree never exceeds its subtree capacity. -/
theorem DenseTree.length_le_capacity {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T} {depth len : Nat}
    (h : DenseTree packing_factor tree depth len) :
    len ≤ subtreeCapacity packing_factor depth := by
  induction h with
  | zero => simp [subtreeCapacity]
  | leaf => simp [subtreeCapacity, leafCapacity]
  | packed factor pl hpos hfit => simpa [subtreeCapacity, leafCapacity]
  | node packing_factor rl left right child_depth left_len right_len
      hleft hright hleftpos hfull ihleft ihright =>
    by_cases hrightpos : 0 < right_len
    · have hleftfull := hfull hrightpos
      rw [hleftfull]
      have hcap : subtreeCapacity packing_factor (child_depth + 1) =
          2 * subtreeCapacity packing_factor child_depth := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
      rw [hcap]
      omega
    · have hrightzero : right_len = 0 := by omega
      subst right_len
      have hcap : subtreeCapacity packing_factor (child_depth + 1) =
          2 * subtreeCapacity packing_factor child_depth := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
      rw [hcap]
      omega

/-- A dense tree's depth and length indices are uniquely determined. -/
theorem DenseTree.indices_unique {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T}
    {depth₁ len₁ depth₂ len₂ : Nat}
    (h₁ : DenseTree packing_factor tree depth₁ len₁)
    (h₂ : DenseTree packing_factor tree depth₂ len₂) :
    depth₁ = depth₂ ∧ len₁ = len₂ := by
  induction h₁ generalizing depth₂ len₂ with
  | zero packing_factor depth =>
    cases h₂
    exact ⟨rfl, rfl⟩
  | leaf l =>
    cases h₂
    exact ⟨rfl, rfl⟩
  | packed factor pl hpos hfit =>
    cases h₂
    exact ⟨rfl, rfl⟩
  | node packing_factor rl left right child_depth left_len right_len
      hleft hright hleftpos hfull ihleft ihright =>
    cases h₂ with
    | node _ _ _ _ child_depth₂ left_len₂ right_len₂ hleft₂ hright₂ _ _ =>
      obtain ⟨hdepth, hleftlen⟩ := ihleft hleft₂
      obtain ⟨_, hrightlen⟩ := ihright hright₂
      omega

/-- Checked `Usize` addition succeeds when its mathematical sum is the value
    of an existing `Usize`. -/
private theorem usize_add_eq_of_val {x y z : Std.Usize}
    (hval : x.val + y.val = z.val) : x + y = ok z := by
  have hadd := UScalar.add_equiv x y
  cases heq : x + y with
  | fail e =>
    rw [heq] at hadd
    simp at hadd
    have hzbound : z.val < 2 ^ System.Platform.numBits := by
      simpa using z.hBounds
    omega
  | div =>
    rw [heq] at hadd
    simp at hadd
  | ok result =>
    rw [heq] at hadd
    simp at hadd
    have hresult : result = z := by scalar_tac
    exact congrArg ok hresult

/-- Successful checked addition agrees with natural-number addition. -/
private theorem usize_add_val {x y sum : Std.Usize}
    (h : x + y = ok sum) : sum.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  rw [h] at hadd
  simp at hadd
  omega

/-- Successful subtraction by one exposes the predecessor relation. -/
private theorem usize_sub_one_val {x predecessor : Std.Usize}
    (h : x - 1#usize = ok predecessor) :
    x.val = predecessor.val + 1 := by
  have hsub := UScalar.sub_equiv x 1#usize
  rw [h] at hsub
  obtain ⟨-, hone, -⟩ := hsub
  scalar_tac

/-- Successful right shift agrees with `Nat.shiftRight`. -/
private theorem usize_shift_right_val {x shift shifted : Std.Usize}
    (h : x >>> shift = ok shifted) :
    shifted.val = x.val >>> shift.val := by
  have hbound : shift.val < System.Platform.numBits := by
    change UScalar.shiftRight x shift.val = ok shifted at h
    unfold UScalar.shiftRight at h
    split at h
    · assumption
    · simp at h
  have hspec := Std.Usize.ShiftRight_spec x shift hbound
  rw [h] at hspec
  exact hspec.1

/-- Testing routing bit `shift` selects the lower half exactly when the index
    modulo the represented parent capacity lies below the child capacity. -/
private theorem routing_bit_zero_iff {index shift shifted : Std.Usize}
    (hshift : index >>> shift = ok shifted) :
    (shifted &&& 1#usize) = 0#usize ↔
      index.val % (2 ^ (shift.val + 1)) < 2 ^ shift.val := by
  have hshifted := usize_shift_right_val hshift
  have hnat :
      ((index.val >>> shift.val) &&& 1 = 0) ↔
        index.val % (2 ^ (shift.val + 1)) < 2 ^ shift.val := by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, pow_succ]
    rw [← Nat.mod_mul_right_div_self]
    exact Nat.div_eq_zero_iff_lt (Nat.two_pow_pos shift.val)
  constructor
  · intro hbit
    apply hnat.mp
    have hbitval := congrArg UScalar.val hbit
    simpa [hshifted] using hbitval
  · intro hleft
    have hbitval := hnat.mpr hleft
    apply UScalar.eq_of_val_eq
    simpa [hshifted] using hbitval

/-- Reducing modulo a child capacity after the parent capacity changes
    nothing when the parent remainder selects the left child. -/
private theorem mod_child_eq_parent_of_lt (index child_capacity : Nat)
    (hchild : 0 < child_capacity)
    (hleft : index % (child_capacity * 2) < child_capacity) :
    index % child_capacity = index % (child_capacity * 2) := by
  calc
    index % child_capacity =
        (index % (child_capacity * 2)) % child_capacity := by
          symm
          exact Nat.mod_mul_right_mod index child_capacity 2
    _ = index % (child_capacity * 2) := Nat.mod_eq_of_lt hleft

/-- In the right half, reducing modulo the child capacity subtracts exactly
    one child capacity from the parent remainder. -/
private theorem mod_child_eq_parent_sub_of_not_lt (index child_capacity : Nat)
    (hchild : 0 < child_capacity)
    (hright : ¬ index % (child_capacity * 2) < child_capacity) :
    index % child_capacity =
      index % (child_capacity * 2) - child_capacity := by
  let remainder := index % (child_capacity * 2)
  have hremainder_lt : remainder < child_capacity * 2 :=
    Nat.mod_lt index (by omega)
  have hremainder_ge : child_capacity ≤ remainder := by omega
  calc
    index % child_capacity = remainder % child_capacity := by
      exact (Nat.mod_mul_right_mod index child_capacity 2).symm
    _ = (remainder - child_capacity) % child_capacity :=
      Nat.mod_eq_sub_mod hremainder_ge
    _ = remainder - child_capacity := Nat.mod_eq_of_lt (by omega)

/-- A natural-number remainder of zero yields the corresponding successful
    translated `Usize` operation. -/
private theorem usize_rem_eq_zero {index factor : Std.Usize}
    (hfactor : 0 < factor.val) (hrem : index.val % factor.val = 0) :
    index % factor = ok 0#usize := by
  have hspec := Std.Usize.rem_bv_spec index (Nat.ne_of_gt hfactor)
  cases heq : index % factor with
  | fail e => rw [heq] at hspec; simp at hspec
  | div => rw [heq] at hspec; simp at hspec
  | ok remainder =>
    rw [heq] at hspec
    have hremainder : remainder = 0#usize := by
      have := hspec.1
      scalar_tac
    exact congrArg ok hremainder

/-- `Tree.compute_len` agrees with the logical length carried by `DenseTree`,
    provided that logical length is represented by the supplied `Usize`. -/
theorem DenseTree.compute_len_eq {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize} {tree : Tree T} {depth len : Nat}
    (hdense : DenseTree packing_factor tree depth len)
    (length : Std.Usize) (hlength : length.val = len) :
    Tree.compute_len ValueInst tree = ok length := by
  induction hdense generalizing length with
  | zero packing_factor zero_depth =>
    have hzero : length = 0#usize := by scalar_tac
    subst length
    simp [Tree.compute_len]
  | leaf l =>
    have hone : length = 1#usize := by scalar_tac
    subst length
    simp [Tree.compute_len]
  | packed factor pl hpos hfit =>
    have hlen : alloc.vec.Vec.len pl.values = length := by scalar_tac
    simp [Tree.compute_len, hlen]
  | node packing_factor rl left right child_depth left_len right_len
      hleft hright hleftpos hfull ihleft ihright =>
    let left_length : Std.Usize := Usize.ofNatCore left_len (by
      have hbound : length.val < 2 ^ UScalarTy.Usize.numBits := length.hBounds
      scalar_tac)
    let right_length : Std.Usize := Usize.ofNatCore right_len (by
      have hbound : length.val < 2 ^ UScalarTy.Usize.numBits := length.hBounds
      scalar_tac)
    have hleftval : left_length.val = left_len := by
      simp [left_length]
    have hrightval : right_length.val = right_len := by
      simp [right_length]
    have hleftcompute := ihleft left_length hleftval
    have hrightcompute := ihright right_length hrightval
    have hadd : left_length + right_length = ok length :=
      usize_add_eq_of_val (by simp [hleftval, hrightval, hlength])
    unfold Tree.compute_len
    simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
      hleftcompute, hrightcompute, hadd]

/-- A dense-prefix bound implies the local path condition used by the
    update/read roundtrip theorem. The modulo form makes the lemma valid for a
    subtree reached below the root as well as for a whole tree. -/
theorem DenseTree.updateIndexWithinLength_of_mod_le {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize} {tree : Tree T} {depth len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth len)
    (machine_depth : Std.Usize) (hdepth : machine_depth.val = depth)
    (index : Std.Usize)
    (hindex : index.val % subtreeCapacity packing_factor depth ≤ len) :
    updateIndexWithinLength ValueInst tree index machine_depth packing_depth := by
  induction hdense generalizing machine_depth with
  | zero packing_factor zero_depth =>
    intro actual_factor hactual
    have hfactor_query := hlayout.opt_packing_factor_eq
    rw [hfactor_query] at hactual
    cases packing_factor with
    | none => simp at hactual
    | some factor =>
      simp at hactual
      subst actual_factor
      have hfactor_pos : 0 < factor.val := by
        simpa [leafCapacity] using hlayout.leafCapacity_pos
      have hcapacity : subtreeCapacity (some factor) zero_depth.val =
          factor.val * 2 ^ zero_depth.val := by
        simp [subtreeCapacity, leafCapacity]
      have hmod_capacity :
          index.val % subtreeCapacity (some factor) zero_depth.val = 0 := by
        omega
      have hfactor_dvd : factor.val ∣
          subtreeCapacity (some factor) zero_depth.val := by
        refine ⟨2 ^ zero_depth.val, ?_⟩
        exact hcapacity
      have hmod_factor := Nat.mod_mod_of_dvd index.val hfactor_dvd
      rw [hmod_capacity] at hmod_factor
      simp at hmod_factor
      refine ⟨0#usize, 0#usize,
        usize_rem_eq_zero hfactor_pos hmod_factor, ?_, by simp⟩
      simp [Tree.compute_len]
  | leaf l => trivial
  | packed factor leaf values_nonempty values_fit => trivial
  | node packing_factor rl left right child_depth left_len right_len
      left_dense right_dense left_nonempty left_full_before_right
      ihleft ihright =>
    unfold updateIndexWithinLength
    have hdepth_pos : machine_depth > 0#usize := by scalar_tac
    rw [if_pos hdepth_pos]
    cases hnew_depth : machine_depth - 1#usize with
    | fail e => simp
    | div => simp
    | ok new_depth =>
      simp only
      cases hshift : new_depth + packing_depth with
      | fail e => simp
      | div => simp
      | ok shift =>
        simp only
        cases hshifted : index >>> shift with
        | fail e => simp
        | div => simp
        | ok shifted =>
          simp only
          have hnew_depth_val : new_depth.val = child_depth := by
            have hpred := usize_sub_one_val hnew_depth
            omega
          have hshift_val : shift.val = packing_depth.val + child_depth := by
            have hadd := usize_add_val hshift
            omega
          have hchild_capacity :
              subtreeCapacity packing_factor child_depth = 2 ^ shift.val := by
            rw [hlayout.subtreeCapacity_eq_two_pow]
            congr 1
            omega
          have hparent_capacity :
              subtreeCapacity packing_factor (child_depth + 1) =
                2 ^ (shift.val + 1) := by
            rw [hlayout.subtreeCapacity_eq_two_pow]
            congr 1
            omega
          split
          · next hbit =>
            have hroute := (routing_bit_zero_iff hshifted).mp hbit
            rw [← hchild_capacity, ← hparent_capacity] at hroute
            have hchild_mod :
                index.val % subtreeCapacity packing_factor child_depth =
                  index.val %
                    subtreeCapacity packing_factor (child_depth + 1) := by
              rw [hchild_capacity, hparent_capacity, pow_succ]
              exact mod_child_eq_parent_of_lt index.val (2 ^ shift.val)
                (Nat.two_pow_pos shift.val) (by simpa [pow_succ] using
                  (routing_bit_zero_iff hshifted).mp hbit)
            have hright_bound := right_dense.length_le_capacity
            have hleft_bound := left_dense.length_le_capacity
            have hlocal :
                index.val % subtreeCapacity packing_factor child_depth ≤
                  left_len := by
              rw [hchild_mod]
              by_cases hright_pos : 0 < right_len
              · have hleft_full := left_full_before_right hright_pos
                omega
              · have hright_zero : right_len = 0 := by omega
                omega
            exact ihleft hlayout new_depth hnew_depth_val hlocal
          · next hbit =>
            have hroute : ¬ index.val % (2 ^ (shift.val + 1)) <
                2 ^ shift.val := by
              intro hleft
              exact hbit ((routing_bit_zero_iff hshifted).mpr hleft)
            have hchild_mod :
                index.val % subtreeCapacity packing_factor child_depth =
                  index.val %
                    subtreeCapacity packing_factor (child_depth + 1) -
                      subtreeCapacity packing_factor child_depth := by
              rw [hchild_capacity, hparent_capacity, pow_succ]
              exact mod_child_eq_parent_sub_of_not_lt index.val
                (2 ^ shift.val) (Nat.two_pow_pos shift.val)
                (by simpa [pow_succ] using hroute)
            have hright_bound := right_dense.length_le_capacity
            have hleft_bound := left_dense.length_le_capacity
            have hparent_route :
                subtreeCapacity packing_factor child_depth ≤
                  index.val %
                    subtreeCapacity packing_factor (child_depth + 1) := by
              rw [hchild_capacity, hparent_capacity]
              omega
            have hlocal :
                index.val % subtreeCapacity packing_factor child_depth ≤
                  right_len := by
              rw [hchild_mod]
              by_cases hright_pos : 0 < right_len
              · have hleft_full := left_full_before_right hright_pos
                omega
              · have hright_zero : right_len = 0 := by omega
                omega
            exact ihright hlayout new_depth hnew_depth_val hlocal

/-- Root-level form of `updateIndexWithinLength_of_mod_le`. -/
theorem DenseTree.updateIndexWithinLength {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth depth : Std.Usize} {tree : Tree T} {len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth.val len)
    (index : Std.Usize) (hindex : index.val ≤ len) :
    updateIndexWithinLength ValueInst tree index depth packing_depth := by
  apply hdense.updateIndexWithinLength_of_mod_le hlayout depth rfl index
  by_cases hfull_index : index.val <
      subtreeCapacity packing_factor depth.val
  · rw [Nat.mod_eq_of_lt hfull_index]
    exact hindex
  · have hcapacity := hdense.length_le_capacity
    have hindex_eq : index.val = subtreeCapacity packing_factor depth.val := by
      omega
    rw [hindex_eq, Nat.mod_self]
    omega

/-! ## Dense reads -/

/-- Subtraction of one from a positive `Usize` succeeds. -/
private theorem usize_sub_one_succeeds {x : Std.Usize} (h : 0 < x.val) :
    ∃ predecessor, x - 1#usize = ok predecessor ∧
      x.val = predecessor.val + 1 := by
  have hsub := UScalar.sub_equiv x 1#usize
  cases heq : x - 1#usize with
  | fail e => rw [heq] at hsub; scalar_tac
  | div => rw [heq] at hsub; simp at hsub
  | ok predecessor =>
    rw [heq] at hsub
    obtain ⟨-, hval, -⟩ := hsub
    exact ⟨predecessor, rfl, by scalar_tac⟩

/-- Addition succeeds when the mathematical sum stays in bounds. -/
private theorem usize_add_succeeds {x y : Std.Usize}
    (h : x.val + y.val < 2 ^ System.Platform.numBits) :
    ∃ sum, x + y = ok sum ∧ sum.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  cases heq : x + y with
  | fail e => rw [heq] at hadd; simp at hadd; scalar_tac
  | div => rw [heq] at hadd; simp at hadd
  | ok sum =>
    rw [heq] at hadd
    simp at hadd
    exact ⟨sum, rfl, by omega⟩

/-- Right shift succeeds for shift amounts below the word size. -/
private theorem usize_shift_right_succeeds (x : Std.Usize)
    {shift : Std.Usize} (h : shift.val < System.Platform.numBits) :
    ∃ shifted, x >>> shift = ok shifted ∧
      shifted.val = x.val >>> shift.val := by
  have hspec := Std.Usize.ShiftRight_spec x shift h
  cases heq : x >>> shift with
  | fail e => rw [heq] at hspec; simp at hspec
  | div => rw [heq] at hspec; simp at hspec
  | ok shifted =>
    rw [heq] at hspec
    exact ⟨shifted, rfl, hspec.1⟩

/-- Remainder by a positive divisor succeeds. -/
private theorem usize_rem_succeeds (x : Std.Usize) {factor : Std.Usize}
    (h : 0 < factor.val) :
    ∃ remainder, x % factor = ok remainder ∧
      remainder.val = x.val % factor.val := by
  have hspec := Std.Usize.rem_bv_spec x (Nat.ne_of_gt h)
  cases heq : x % factor with
  | fail e => rw [heq] at hspec; simp at hspec
  | div => rw [heq] at hspec; simp at hspec
  | ok remainder =>
    rw [heq] at hspec
    exact ⟨remainder, rfl, hspec.1⟩

/-- Reads on a dense tree are characterized by the dense length: an index
    (reduced modulo the subtree capacity, so the statement recurses through
    subtrees) below the length reads a materialized value, and an index at or
    above it reads `none`. `hbits` bounds the routing shifts checked by the
    translated code; containers guarantee it from their type-level maximum
    lengths. -/
theorem DenseTree.get_recursive_spec_of_mod {T : Type}
    {ValueInst : Value T} {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize} {tree : Tree T} {depth len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth len)
    (machine_depth : Std.Usize) (hdepth : machine_depth.val = depth)
    (hbits : depth + packing_depth.val ≤ System.Platform.numBits)
    (index : Std.Usize) :
    (index.val % subtreeCapacity packing_factor depth < len →
      ∃ value, Tree.get_recursive ValueInst tree index machine_depth
        packing_depth = ok (some value)) ∧
    (len ≤ index.val % subtreeCapacity packing_factor depth →
      Tree.get_recursive ValueInst tree index machine_depth packing_depth =
        ok none) := by
  induction hdense generalizing machine_depth with
  | zero packing_factor zero_depth =>
    constructor
    · intro h
      omega
    · intro h
      unfold Tree.get_recursive
      simp
  | leaf l =>
    have hzero : machine_depth = 0#usize := by scalar_tac
    subst hzero
    constructor
    · intro h
      refine ⟨l.value, ?_⟩
      unfold Tree.get_recursive
      simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
    · intro h
      simp [subtreeCapacity, leafCapacity] at h
      omega
  | packed factor pl values_nonempty values_fit =>
    have hzero : machine_depth = 0#usize := by scalar_tac
    subst hzero
    have hfactor := hlayout.tree_hash_packing_factor_eq
    have hfactor_pos : 0 < factor.val := by
      simpa [leafCapacity] using hlayout.leafCapacity_pos
    obtain ⟨sub, hrem, hsub⟩ := usize_rem_succeeds index hfactor_pos
    have hcap : subtreeCapacity (some factor) 0 = factor.val := by
      simp [subtreeCapacity, leafCapacity]
    constructor
    · intro h
      rw [hcap] at h
      have hlt : sub.val < pl.values.val.length := by omega
      refine ⟨pl.values.val[sub.val], ?_⟩
      unfold Tree.get_recursive
      simp [hfactor, hrem, core.slice.Slice.get, alloc.vec.Vec.deref,
        List.getElem?_eq_getElem hlt]
    · intro h
      rw [hcap] at h
      have hge : pl.values.val.length ≤ sub.val := by omega
      unfold Tree.get_recursive
      simp [hfactor, hrem, core.slice.Slice.get, alloc.vec.Vec.deref, hge]
  | node packing_factor rl left right child_depth left_len right_len
      left_dense right_dense left_nonempty left_full_before_right
      ihleft ihright =>
    have hdepth_pos : machine_depth > 0#usize := by scalar_tac
    obtain ⟨nd, hnd, hnd_val⟩ := usize_sub_one_succeeds
      (show 0 < machine_depth.val by scalar_tac)
    have hnd_depth : nd.val = child_depth := by omega
    have hnumbits : System.Platform.numBits < 2 ^ System.Platform.numBits :=
      Nat.lt_two_pow_self
    obtain ⟨sh, hsh, hsh_val⟩ := usize_add_succeeds
      (x := nd) (y := packing_depth) (by omega)
    have hsh_bound : sh.val < System.Platform.numBits := by omega
    obtain ⟨shifted, hshr, hshifted⟩ := usize_shift_right_succeeds index
      hsh_bound
    have hchild_capacity :
        subtreeCapacity packing_factor child_depth = 2 ^ sh.val := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    have hparent_capacity :
        subtreeCapacity packing_factor (child_depth + 1) =
          2 ^ (sh.val + 1) := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    have hleft_bound := left_dense.length_le_capacity
    have hright_bound := right_dense.length_le_capacity
    by_cases hbit : (shifted &&& 1#usize) = 0#usize
    · -- The read routes into the left child.
      have hroute := (routing_bit_zero_iff hshr).mp hbit
      rw [← hchild_capacity, ← hparent_capacity] at hroute
      have hchild_mod :
          index.val % subtreeCapacity packing_factor child_depth =
            index.val % subtreeCapacity packing_factor (child_depth + 1) := by
        rw [hchild_capacity, hparent_capacity, pow_succ]
        refine mod_child_eq_parent_of_lt index.val (2 ^ sh.val)
          (Nat.two_pow_pos sh.val) ?_
        rw [← pow_succ, ← hparent_capacity, ← hchild_capacity]
        exact hroute
      obtain ⟨ih_some, ih_none⟩ := ihleft hlayout nd hnd_depth (by omega)
      constructor
      · intro h
        have hlocal :
            index.val % subtreeCapacity packing_factor child_depth <
              left_len := by
          by_cases hright_pos : 0 < right_len
          · have := left_full_before_right hright_pos
            omega
          · omega
        obtain ⟨value, hvalue⟩ := ih_some hlocal
        refine ⟨value, ?_⟩
        unfold Tree.get_recursive
        rw [if_pos hdepth_pos]
        simp only [hnd, hsh, hshr, lift, bind_tc_ok,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_pos hbit]
        exact hvalue
      · intro h
        have hlocal : left_len ≤
            index.val % subtreeCapacity packing_factor child_depth := by
          omega
        unfold Tree.get_recursive
        rw [if_pos hdepth_pos]
        simp only [hnd, hsh, hshr, lift, bind_tc_ok,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_pos hbit]
        exact ih_none hlocal
    · -- The read routes into the right child.
      have hroute : ¬ index.val % (2 ^ (sh.val + 1)) < 2 ^ sh.val := by
        intro hlt
        exact hbit ((routing_bit_zero_iff hshr).mpr hlt)
      have hparent_route :
          subtreeCapacity packing_factor child_depth ≤
            index.val % subtreeCapacity packing_factor (child_depth + 1) := by
        rw [hchild_capacity, hparent_capacity]
        omega
      have hchild_mod :
          index.val % subtreeCapacity packing_factor child_depth =
            index.val % subtreeCapacity packing_factor (child_depth + 1) -
              subtreeCapacity packing_factor child_depth := by
        rw [hchild_capacity, hparent_capacity, pow_succ]
        exact mod_child_eq_parent_sub_of_not_lt index.val (2 ^ sh.val)
          (Nat.two_pow_pos sh.val) (by simpa [pow_succ] using hroute)
      obtain ⟨ih_some, ih_none⟩ := ihright hlayout nd hnd_depth (by omega)
      constructor
      · intro h
        have hright_pos : 0 < right_len := by
          by_contra hzero
          omega
        have hleft_full := left_full_before_right hright_pos
        have hlocal :
            index.val % subtreeCapacity packing_factor child_depth <
              right_len := by
          omega
        obtain ⟨value, hvalue⟩ := ih_some hlocal
        refine ⟨value, ?_⟩
        unfold Tree.get_recursive
        rw [if_pos hdepth_pos]
        simp only [hnd, hsh, hshr, lift, bind_tc_ok,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_neg hbit]
        exact hvalue
      · intro h
        have hlocal : right_len ≤
            index.val % subtreeCapacity packing_factor child_depth := by
          by_cases hright_pos : 0 < right_len
          · have := left_full_before_right hright_pos
            omega
          · omega
        unfold Tree.get_recursive
        rw [if_pos hdepth_pos]
        simp only [hnd, hsh, hshr, lift, bind_tc_ok,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_neg hbit]
        exact ih_none hlocal

/-- For `index < len`, `get_recursive` on a dense tree returns a
    materialized value. -/
theorem DenseTree.get_recursive_some {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth depth : Std.Usize}
    {tree : Tree T} {len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth.val len)
    (hbits : depth.val + packing_depth.val ≤ System.Platform.numBits)
    (index : Std.Usize) (hindex : index.val < len) :
    ∃ value, Tree.get_recursive ValueInst tree index depth packing_depth =
      ok (some value) := by
  apply (hdense.get_recursive_spec_of_mod hlayout depth rfl hbits index).1
  have hcap := hdense.length_le_capacity
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hindex

/-- For `len ≤ index < capacity`, `get_recursive` on a dense tree returns
    `none`. -/
theorem DenseTree.get_recursive_none {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth depth : Std.Usize}
    {tree : Tree T} {len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth.val len)
    (hbits : depth.val + packing_depth.val ≤ System.Platform.numBits)
    (index : Std.Usize) (hlen : len ≤ index.val)
    (hcap : index.val < subtreeCapacity packing_factor depth.val) :
    Tree.get_recursive ValueInst tree index depth packing_depth = ok none := by
  apply (hdense.get_recursive_spec_of_mod hlayout depth rfl hbits index).2
  rw [Nat.mod_eq_of_lt hcap]
  exact hlen

/-- Length zero is represented canonically by a `Zero` node. -/
theorem DenseTree.eq_zero_of_length_zero {T : Type}
    {packing_factor : Option Std.Usize} {tree : Tree T} {depth len : Nat}
    (h : DenseTree packing_factor tree depth len) (hlen : len = 0) :
    ∃ zero_depth, tree = Tree.Zero zero_depth ∧ depth = zero_depth.val := by
  cases h with
  | zero packing_factor zero_depth => exact ⟨zero_depth, rfl, rfl⟩
  | leaf => simp at hlen
  | packed factor pl hpos hfit => omega
  | node packing_factor rl left right child_depth left_len right_len
      hleft hright hleftpos hfull => omega

/-- Trees without padding nodes. -/
inductive NoZero {T : Type} : Tree T → Prop where
  | leaf (l : leaf.Leaf T) : NoZero (Tree.Leaf l)
  | packed (pl : packed_leaf.PackedLeaf T) : NoZero (Tree.PackedLeaf pl)
  | node
      (rl : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (left right : triomphe.arc.Arc (Tree T)) :
      NoZero left → NoZero right → NoZero (Tree.Node rl left right)

/-- A dense tree at full capacity contains no `Zero` padding. -/
theorem DenseTree.noZero_of_full {T : Type} {ValueInst : Value T}
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    {tree : Tree T} {depth len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth len)
    (hfull : len = subtreeCapacity packing_factor depth) :
    NoZero tree := by
  induction hdense with
  | zero packing_factor zero_depth =>
    have hpos := hlayout.subtreeCapacity_pos zero_depth.val
    omega
  | leaf l => exact NoZero.leaf l
  | packed factor pl hpos hfit => exact NoZero.packed pl
  | node packing_factor rl left right child_depth left_len right_len
      hleft hright hleftpos hrightfull ihleft ihright =>
    have hleftcap := hleft.length_le_capacity
    have hrightcap := hright.length_le_capacity
    have hcap : subtreeCapacity packing_factor (child_depth + 1) =
        2 * subtreeCapacity packing_factor child_depth := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc, Nat.mul_comm]
    have hrightpos : 0 < right_len := by
      have hpos := hlayout.subtreeCapacity_pos child_depth
      rw [hcap] at hfull
      omega
    have hleftfull := hrightfull hrightpos
    have hrightfull' : right_len =
        subtreeCapacity packing_factor child_depth := by
      rw [hcap, hleftfull] at hfull
      omega
    exact NoZero.node rl left right
      (ihleft hlayout hleftfull) (ihright hlayout hrightfull')

/-! ## Initial preservation lemmas -/

/-- Inversion for the translated vector push operation. -/
private theorem vec_push_eq_ok {T : Type} {values : alloc.vec.Vec T}
    {value : T} {updated : alloc.vec.Vec T}
    (h : alloc.vec.Vec.push values value = ok updated) :
    updated.val = values.val ++ [value] := by
  unfold alloc.vec.Vec.push at h
  grind

/-- Inversion for a successful `Result` bind. -/
private theorem result_bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- A successful in-place packed-leaf insertion either replaces an existing
    vector element or appends exactly one element. -/
private theorem packedLeaf_insert_mut_length {T : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {leaf updated : packed_leaf.PackedLeaf T} {sub : Std.Usize} {value : T}
    (h : packed_leaf.PackedLeaf.insert_mut thi cloneInst leaf sub value =
      ok (core.result.Result.Ok (), updated)) :
    updated.values.val.length =
        (if sub.val = leaf.values.val.length
        then leaf.values.val.length + 1
        else leaf.values.val.length) ∧
      sub.val ≤ leaf.values.val.length := by
  unfold packed_leaf.PackedLeaf.insert_mut at h
  simp [lock_api.rwlock.RwLock.get_mut,
    alloy_primitives.bits.fixed.FixedBytes.ZERO] at h
  split at h
  · next heq =>
    cases hpush : alloc.vec.Vec.push leaf.values value with
    | fail e => rw [hpush] at h; simp at h
    | div => rw [hpush] at h; simp at h
    | ok values =>
      rw [hpush] at h
      simp at h
      subst h
      have hvalues := vec_push_eq_ok hpush
      have hsub : sub.val = leaf.values.val.length := by scalar_tac
      simp [hsub, hvalues]
  · next hne =>
    split at h
    · next hlt =>
      cases hindex : alloc.vec.Vec.index_mut_usize leaf.values sub with
      | fail e => rw [hindex] at h; simp at h
      | div => rw [hindex] at h; simp at h
      | ok pair =>
        rw [hindex] at h
        obtain ⟨element, back⟩ := pair
        simp at h
        unfold alloc.vec.Vec.index_mut_usize at hindex
        split at hindex <;>
          simp only [ok.injEq, Prod.mk.injEq, reduceCtorEq] at hindex
        obtain ⟨-, hback⟩ := hindex
        subst hback
        subst h
        have hsub_ne : sub.val ≠ leaf.values.val.length := by
          intro heqval
          apply hne
          scalar_tac
        simp [hsub_ne]
        omega
    · simp at h

/-- The value of a successful `Usize` remainder is the corresponding natural
    number remainder. -/
private theorem usize_rem_val {x y remainder : Std.Usize}
    (y_pos : 0 < y.val) (h : x % y = ok remainder) :
    remainder.val = x.val % y.val := by
  have hspec := Std.Usize.rem_bv_spec x (Nat.ne_of_gt y_pos)
  rw [h] at hspec
  exact hspec.1

/-- A successful functional packed-leaf insertion has the same replace/append
    length behavior as its `insert_mut` helper. -/
private theorem packedLeaf_insert_at_index_length {T : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {leaf updated : packed_leaf.PackedLeaf T} {index : Std.Usize} {value : T}
    (h : packed_leaf.PackedLeaf.insert_at_index thi cloneInst leaf index value =
      ok (core.result.Result.Ok updated)) :
    ∃ factor sub,
      thi.tree_hash_packing_factor = ok factor ∧
      index % factor = ok sub ∧
      updated.values.val.length =
        (if sub.val = leaf.values.val.length
        then leaf.values.val.length + 1
        else leaf.values.val.length) ∧
      sub.val ≤ leaf.values.val.length := by
  unfold packed_leaf.PackedLeaf.insert_at_index at h
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new] at h
  simp only [result_bind_eq_ok_iff] at h
  obtain ⟨cloned, hclone, factor, hfactor, sub, hsub,
    ⟨result, candidate⟩, hinsert, h⟩ := h
  cases result with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
  | Ok success =>
    cases success
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    subst h
    have hlength := packedLeaf_insert_mut_length hinsert
    have hclone_length : cloned.val.length = leaf.values.val.length := by
      exact Aeneas.Std.Slice.clone_length hclone
    simp [hclone_length] at hlength
    exact ⟨factor, sub, hfactor, hsub, hlength⟩

/-- `Tree.zero` constructs the canonical dense tree of length zero. -/
theorem zero_preserves_dense {T : Type} (ValueInst : Value T)
    (packing_factor : Option Std.Usize) (depth : Std.Usize) :
    ∃ tree, Tree.zero ValueInst depth = ok tree ∧
      DenseTree packing_factor tree depth.val 0 := by
  refine ⟨Tree.Zero depth, ?_, DenseTree.zero packing_factor depth⟩
  rfl

/-- `Tree.empty` is the same canonical zero tree as `Tree.zero`. -/
theorem empty_preserves_dense {T : Type} (ValueInst : Value T)
    (packing_factor : Option Std.Usize) (depth : Std.Usize) :
    ∃ tree, Tree.empty ValueInst depth = ok tree ∧
      DenseTree packing_factor tree depth.val 0 := by
  exact zero_preserves_dense ValueInst packing_factor depth

/-- The unboxed zero constructor also produces a dense tree of length zero. -/
theorem zero_unboxed_preserves_dense {T : Type} (ValueInst : Value T)
    (packing_factor : Option Std.Usize) (depth : Std.Usize) :
    ∃ tree, Tree.zero_unboxed ValueInst depth = ok tree ∧
      DenseTree packing_factor tree depth.val 0 := by
  exact ⟨Tree.Zero depth, rfl, DenseTree.zero packing_factor depth⟩

/-- `Tree.leaf` produces an unpacked dense tree containing one value. -/
theorem leaf_preserves_dense {T : Type} (ValueInst : Value T) (value : T) :
    ∃ tree, Tree.leaf ValueInst value = ok tree ∧
      DenseTree none tree 0 1 := by
  unfold Tree.leaf leaf.Leaf.new leaf.Leaf.with_hash
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
  exact DenseTree.leaf _

/-- `Tree.leaf_with_hash` produces an unpacked dense tree containing one
    value; the supplied cache has no bearing on density. -/
theorem leaf_with_hash_preserves_dense {T : Type} (ValueInst : Value T)
    (value : T) (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    ∃ tree, Tree.leaf_with_hash ValueInst value hash = ok tree ∧
      DenseTree none tree 0 1 := by
  unfold Tree.leaf_with_hash leaf.Leaf.with_hash
  simp [lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
  exact DenseTree.leaf _

/-- The unboxed leaf constructor produces an unpacked dense tree containing
    one value. -/
theorem leaf_unboxed_preserves_dense {T : Type} (ValueInst : Value T)
    (value : T) :
    ∃ tree, Tree.leaf_unboxed ValueInst value = ok tree ∧
      DenseTree none tree 0 1 := by
  unfold Tree.leaf_unboxed leaf.Leaf.new leaf.Leaf.with_hash
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
  exact DenseTree.leaf _

/-- A singleton packed leaf is dense. The packing layout supplies both the
    raw factor expected by the translated constructor and its positivity. -/
theorem packedLeaf_single_preserves_dense {T : Type}
    (ValueInst : Value T) {factor packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst (some factor) packing_depth)
    (value : T) :
    ∃ leaf,
      packed_leaf.PackedLeaf.single ValueInst.tree_hashTreeHashInst
        ValueInst.corecloneCloneInst value = ok leaf ∧
      DenseTree (some factor) (Tree.PackedLeaf leaf) 0 1 := by
  unfold packed_leaf.PackedLeaf.single
  rw [hlayout.tree_hash_packing_factor_eq]
  cases hpush : alloc.vec.Vec.push
      (alloc.vec.Vec.with_capacity T factor) value with
  | fail e =>
    unfold alloc.vec.Vec.push at hpush
    simp [alloc.vec.Vec.with_capacity] at hpush
    grind
  | div =>
    unfold alloc.vec.Vec.push at hpush
    simp [alloc.vec.Vec.with_capacity] at hpush
    grind
  | ok values =>
    have hvalues := vec_push_eq_ok hpush
    have hfactor_pos : 0 < factor.val := by
      simpa [leafCapacity] using hlayout.leafCapacity_pos
    simp [hpush, alloy_primitives.bits.fixed.FixedBytes.ZERO,
      lock_api.rwlock.RwLock.new]
    have hdense := DenseTree.packed factor
      ({ hash := Array.repeat 32#usize 0#u8, values := values } :
        packed_leaf.PackedLeaf T)
      (by simp [hvalues, alloc.vec.Vec.with_capacity])
      (by simp [hvalues, alloc.vec.Vec.with_capacity]; omega)
    simpa [hvalues, alloc.vec.Vec.with_capacity] using hdense

/-- `PackedLeaf.insert_at_index` preserves packed-leaf density. A successful
    call replaces an existing slot, or appends exactly when the computed
    packed sub-index is the old leaf length. -/
theorem packedLeaf_insert_at_index_preserves_dense {T : Type}
    (ValueInst : Value T) {factor packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst (some factor) packing_depth)
    {leaf updated : packed_leaf.PackedLeaf T} {len : Nat}
    (hdense : DenseTree (some factor) (Tree.PackedLeaf leaf) 0 len)
    (index : Std.Usize) (value : T)
    (hinsert : packed_leaf.PackedLeaf.insert_at_index
      ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst
      leaf index value = ok (core.result.Result.Ok updated)) :
    DenseTree (some factor) (Tree.PackedLeaf updated) 0
        updated.values.val.length ∧
      ∃ sub, index % factor = ok sub ∧
        updated.values.val.length =
          (if sub.val = len then len + 1 else len) := by
  cases hdense with
  | packed _ _ old_nonempty old_fit =>
    obtain ⟨actual_factor, sub, hfactor, hsub, hlength, hsub_le⟩ :=
      packedLeaf_insert_at_index_length hinsert
    have hraw_factor := hlayout.tree_hash_packing_factor_eq
    have hfactor_eq : actual_factor = factor := by
      rw [hraw_factor] at hfactor
      simp at hfactor
      exact hfactor.symm
    subst actual_factor
    have hfactor_pos : 0 < factor.val := by
      simpa [leafCapacity] using hlayout.leafCapacity_pos
    have hsub_val := usize_rem_val hfactor_pos hsub
    have hsub_lt : sub.val < factor.val := by
      rw [hsub_val]
      exact Nat.mod_lt index.val hfactor_pos
    have hnew_nonempty : 0 < updated.values.val.length := by
      rw [hlength]
      split <;> omega
    have hnew_fit : updated.values.val.length ≤ factor.val := by
      rw [hlength]
      split <;> omega
    refine ⟨DenseTree.packed factor updated hnew_nonempty hnew_fit,
      sub, hsub, ?_⟩
    simpa using hlength

/-- `Tree.node` preserves density when the two child judgments satisfy the
    left-prefix side conditions of `DenseTree.node`. -/
theorem node_preserves_dense {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize}
    (left right : triomphe.arc.Arc (Tree T))
    (hash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (child_depth left_len right_len : Nat)
    (left_dense : DenseTree packing_factor left child_depth left_len)
    (right_dense : DenseTree packing_factor right child_depth right_len)
    (left_nonempty : 0 < left_len)
    (left_full_before_right : 0 < right_len →
      left_len = subtreeCapacity packing_factor child_depth) :
    ∃ tree, Tree.node ValueInst left right hash = ok tree ∧
      DenseTree packing_factor tree (child_depth + 1)
        (left_len + right_len) := by
  refine ⟨Tree.Node hash left right, ?_, ?_⟩
  · rfl
  · exact DenseTree.node packing_factor hash left right child_depth
      left_len right_len left_dense right_dense left_nonempty
      left_full_before_right

/-- `Tree.node_unboxed` has the same density rule as `Tree.node`. -/
theorem node_unboxed_preserves_dense {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize}
    (left right : triomphe.arc.Arc (Tree T))
    (child_depth left_len right_len : Nat)
    (left_dense : DenseTree packing_factor left child_depth left_len)
    (right_dense : DenseTree packing_factor right child_depth right_len)
    (left_nonempty : 0 < left_len)
    (left_full_before_right : 0 < right_len →
      left_len = subtreeCapacity packing_factor child_depth) :
    ∃ tree, Tree.node_unboxed ValueInst left right = ok tree ∧
      DenseTree packing_factor tree (child_depth + 1)
        (left_len + right_len) := by
  unfold Tree.node_unboxed
  simp [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    lock_api.rwlock.RwLock.new]
  exact DenseTree.node packing_factor _ left right child_depth left_len
    right_len left_dense right_dense left_nonempty left_full_before_right

/-- The translated `Tree.clone` operation preserves the complete dense-tree
    judgment, including packed-vector length. -/
theorem DenseTree.clone_preserves_dense {T : Type} (ValueInst : Value T)
    {packing_factor : Option Std.Usize} {tree updated : Tree T}
    {depth len : Nat}
    (hdense : DenseTree packing_factor tree depth len)
    (hclone : Tree.Insts.CoreCloneClone.clone ValueInst tree = ok updated) :
    DenseTree packing_factor updated depth len := by
  cases hdense with
  | zero packing_factor zero_depth =>
    simp [Tree.Insts.CoreCloneClone.clone] at hclone
    subst updated
    exact DenseTree.zero packing_factor zero_depth
  | leaf leaf =>
    unfold Tree.Insts.CoreCloneClone.clone at hclone
    simp only [result_bind_eq_ok_iff] at hclone
    obtain ⟨new_leaf, hleaf, hclone⟩ := hclone
    simp at hclone
    subst updated
    exact DenseTree.leaf new_leaf
  | packed factor leaf hnonempty hfit =>
    unfold Tree.Insts.CoreCloneClone.clone
      packed_leaf.PackedLeaf.Insts.CoreCloneClone.clone at hclone
    simp [lock_api.rwlock.RwLock.read,
      lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
      lock_api.rwlock.RwLock.new] at hclone
    simp only [result_bind_eq_ok_iff] at hclone
    obtain ⟨new_values, hvalues, hclone⟩ := hclone
    simp at hclone
    subst updated
    have hlength : new_values.val.length = leaf.values.val.length := by
      exact Aeneas.Std.Slice.clone_length hvalues
    have hnew_nonempty : 0 < new_values.val.length := by omega
    have hnew_fit : new_values.val.length ≤ factor.val := by omega
    have hnew_dense := DenseTree.packed factor
      ({ hash := leaf.hash, values := new_values } : packed_leaf.PackedLeaf T)
      hnew_nonempty hnew_fit
    simpa [hlength] using hnew_dense
  | node packing_factor hash left right child_depth left_len right_len
      left_dense right_dense left_nonempty left_full_before_right =>
    simp [Tree.Insts.CoreCloneClone.clone,
      lock_api.rwlock.RwLock.read,
      lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
      lock_api.rwlock.RwLock.new,
      triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hclone
    subst updated
    exact DenseTree.node packing_factor hash left right child_depth left_len
      right_len left_dense right_dense left_nonempty left_full_before_right

/-! ## Recursive update preservation -/

private def updateZbit {T : Type} : Tree T → Nat
  | Tree.Zero _ => 1
  | _ => 0

private theorem updateZbit_le_one {T : Type} (tree : Tree T) :
    updateZbit tree ≤ 1 := by
  cases tree <;> simp [updateZbit]

private theorem with_updated_leaf_leaf_preserves_dense {T : Type}
    (ValueInst : Value T) (leaf : leaf.Leaf T) (index : Std.Usize)
    (new_value : T) {updated : Tree T}
    (h : Tree.with_updated_leaf ValueInst (Tree.Leaf leaf) index new_value
      0#usize = ok (core.result.Result.Ok updated)) :
    DenseTree none updated 0 1 := by
  obtain ⟨new_tree, hleaf, hdense⟩ :=
    leaf_preserves_dense ValueInst new_value
  unfold Tree.with_updated_leaf at h
  rw [hleaf] at h
  simp at h
  subst updated
  exact hdense

private theorem with_updated_leaf_packed_preserves_dense {T : Type}
    (ValueInst : Value T) {factor packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst (some factor) packing_depth)
    (leaf : packed_leaf.PackedLeaf T) (len : Nat)
    (hdense : DenseTree (some factor) (Tree.PackedLeaf leaf) 0 len)
    (index : Std.Usize) (new_value : T) {updated : Tree T}
    (h : Tree.with_updated_leaf ValueInst (Tree.PackedLeaf leaf) index
      new_value 0#usize = ok (core.result.Result.Ok updated)) :
    DenseTree (some factor) updated 0
      (updatedDenseLength (some factor) 0 index len) := by
  unfold Tree.with_updated_leaf at h
  simp [triomphe.arc.Arc.new] at h
  simp only [result_bind_eq_ok_iff] at h
  obtain ⟨result, hinsert, h⟩ := h
  cases result with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
  | Ok updated_leaf =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    subst h
    obtain ⟨hupdated, sub, hsub, hlength⟩ :=
      packedLeaf_insert_at_index_preserves_dense ValueInst hlayout hdense
        index new_value hinsert
    have hfactor_pos : 0 < factor.val := by
      simpa [leafCapacity] using hlayout.leafCapacity_pos
    have hsub_val := usize_rem_val hfactor_pos hsub
    rw [hlength] at hupdated
    have hmod_lt : index.val % factor.val < factor.val :=
      Nat.mod_lt index.val hfactor_pos
    by_cases hedge : index.val % factor.val = len
    · have hlen_lt : len < factor.val := by omega
      simpa [updatedDenseLength, subtreeCapacity, leafCapacity, hsub_val,
        hedge, hlen_lt] using hupdated
    · simpa [updatedDenseLength, subtreeCapacity, leafCapacity, hsub_val,
        hedge] using hupdated

private theorem with_updated_leaf_preserves_dense_aux {T : Type}
    (ValueInst : Value T) {packing_factor : Option Std.Usize}
    {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (index : Std.Usize) (new_value : T) :
    ∀ (n : Nat) (depth : Std.Usize) (self updated : Tree T)
      (tree_depth len : Nat),
      2 * depth.val + updateZbit self ≤ n →
      depth.val = tree_depth →
      UpdateReady packing_factor self tree_depth len →
      index.val % subtreeCapacity packing_factor tree_depth ≤ len →
      Tree.with_updated_leaf ValueInst self index new_value depth =
        ok (core.result.Result.Ok updated) →
      DenseTree packing_factor updated tree_depth
        (updatedDenseLength packing_factor tree_depth index len) := by
  intro n
  induction n with
  | zero =>
    intro depth self updated tree_depth len hmeasure hdepth hready hindex hupdate
    cases hready with
    | zero packing_factor zero_depth =>
      simp [updateZbit] at hmeasure
    | leaf leaf =>
      have hdepth_zero : depth = 0#usize := by scalar_tac
      subst depth
      simpa [updatedDenseLength, subtreeCapacity, leafCapacity] using
        with_updated_leaf_leaf_preserves_dense ValueInst leaf index new_value
          hupdate
    | packed factor leaf hnonempty hfit =>
      have hdepth_zero : depth = 0#usize := by scalar_tac
      subst depth
      exact with_updated_leaf_packed_preserves_dense ValueInst hlayout leaf
        leaf.values.val.length (DenseTree.packed factor leaf hnonempty hfit)
        index new_value hupdate
    | node packing_factor rl left right child_depth left_len right_len
        left_dense right_dense shape =>
      simp [updateZbit] at hmeasure
      omega
  | succ n ih =>
    intro depth self updated tree_depth len hmeasure hdepth hready hindex hupdate
    cases hready with
    | leaf leaf =>
      have hdepth_zero : depth = 0#usize := by scalar_tac
      subst depth
      simpa [updatedDenseLength, subtreeCapacity, leafCapacity] using
        with_updated_leaf_leaf_preserves_dense ValueInst leaf index new_value
          hupdate
    | packed factor leaf hnonempty hfit =>
      have hdepth_zero : depth = 0#usize := by scalar_tac
      subst depth
      exact with_updated_leaf_packed_preserves_dense ValueInst hlayout leaf
        leaf.values.val.length (DenseTree.packed factor leaf hnonempty hfit)
        index new_value hupdate
    | node packing_factor rl left right child_depth left_len right_len
        left_dense right_dense shape =>
      unfold Tree.with_updated_leaf at hupdate
      have hdepth_pos : depth > 0#usize := by scalar_tac
      simp only [if_pos hdepth_pos] at hupdate
      rw [hlayout.opt_packing_depth_eq] at hupdate
      have hunwrap := hlayout.unwrap_opt_packing_depth_eq
      simp [hunwrap, lift,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone,
        alloy_primitives.bits.fixed.FixedBytes.ZERO,
        lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new, Tree.node] at hupdate
      simp only [result_bind_eq_ok_iff] at hupdate
      obtain ⟨new_depth, hnew_depth, shift, hshift, shifted, hshifted,
        hupdate⟩ := hupdate
      have hnew_depth_val : new_depth.val = child_depth := by
        have hpred := usize_sub_one_val hnew_depth
        omega
      have hshift_val : shift.val = packing_depth.val + child_depth := by
        have hadd := usize_add_val hshift
        omega
      have hchild_capacity :
          subtreeCapacity packing_factor child_depth = 2 ^ shift.val := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      have hparent_capacity :
          subtreeCapacity packing_factor (child_depth + 1) =
            2 ^ (shift.val + 1) := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      have hcapacity_succ :
          subtreeCapacity packing_factor (child_depth + 1) =
            subtreeCapacity packing_factor child_depth * 2 := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
      have hchild_capacity_pos := hlayout.subtreeCapacity_pos child_depth
      have hparent_capacity_pos :=
        hlayout.subtreeCapacity_pos (child_depth + 1)
      have hparent_mod_lt :
          index.val % subtreeCapacity packing_factor (child_depth + 1) <
            subtreeCapacity packing_factor (child_depth + 1) :=
        Nat.mod_lt index.val hparent_capacity_pos
      have hleft_bound := left_dense.length_le_capacity
      have hright_bound := right_dense.length_le_capacity
      split at hupdate
      · next hbit =>
        have hroute := (routing_bit_zero_iff hshifted).mp hbit
        have hroute_capacity :
            index.val %
                subtreeCapacity packing_factor (child_depth + 1) <
              subtreeCapacity packing_factor child_depth := by
          rw [hchild_capacity, hparent_capacity]
          exact hroute
        have hchild_mod :
            index.val % subtreeCapacity packing_factor child_depth =
              index.val %
                subtreeCapacity packing_factor (child_depth + 1) := by
          rw [hchild_capacity, hparent_capacity, pow_succ]
          exact mod_child_eq_parent_of_lt index.val (2 ^ shift.val)
            (Nat.two_pow_pos shift.val) (by simpa [pow_succ] using hroute)
        rw [hcapacity_succ] at hchild_mod hindex hroute_capacity hparent_mod_lt
        have hlocal :
            index.val % subtreeCapacity packing_factor child_depth ≤
              left_len := by
          rw [hchild_mod]
          cases shape with
          | inl hempty => omega
          | inr hdense_shape =>
            by_cases hright_pos : 0 < right_len
            · have hleft_full := hdense_shape.2 hright_pos
              omega
            · omega
        cases hrecursive : Tree.with_updated_leaf ValueInst left index
            new_value new_depth with
        | fail e => rw [hrecursive] at hupdate; simp at hupdate
        | div => rw [hrecursive] at hupdate; simp at hupdate
        | ok result =>
          rw [hrecursive] at hupdate
          cases result with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok new_left =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at hupdate
            subst updated
            have hrecursive_dense := ih new_depth left new_left child_depth
              left_len
              (by have := updateZbit_le_one left; omega)
              hnew_depth_val
              (UpdateReady.ofDense left_dense) hlocal hrecursive
            let new_left_len := updatedDenseLength packing_factor child_depth
              index left_len
            have hnew_left_pos : 0 < new_left_len := by
              unfold new_left_len updatedDenseLength
              split
              · omega
              · cases shape with
                | inl hempty =>
                  rename_i hnotgrow
                  exfalso
                  apply hnotgrow
                  constructor
                  · rw [hchild_mod]
                    omega
                  · omega
                | inr hdense_shape => exact hdense_shape.1
            have hnew_left_full : 0 < right_len →
                new_left_len = subtreeCapacity packing_factor child_depth := by
              intro hright_pos
              cases shape with
              | inl hempty => omega
              | inr hdense_shape =>
                have hleft_full := hdense_shape.2 hright_pos
                unfold new_left_len updatedDenseLength
                simp [hleft_full]
            have hnode_dense : DenseTree packing_factor
                (Tree.Node (Array.repeat 32#usize 0#u8) new_left right)
                (child_depth + 1) (new_left_len + right_len) :=
              DenseTree.node packing_factor _ new_left right child_depth
                new_left_len right_len hrecursive_dense right_dense
                hnew_left_pos hnew_left_full
            have hlength :
                updatedDenseLength packing_factor (child_depth + 1) index
                    (left_len + right_len) = new_left_len + right_len := by
              unfold new_left_len
              unfold updatedDenseLength
              rw [hchild_mod, hcapacity_succ]
              split <;> split <;>
                cases shape with
                | inl hempty => omega
                | inr hdense_shape =>
                  by_cases hright_pos : 0 < right_len
                  · have hleft_full := hdense_shape.2 hright_pos
                    omega
                  · omega
            rw [hlength]
            exact hnode_dense
      · next hbit =>
        have hroute : ¬ index.val % (2 ^ (shift.val + 1)) <
            2 ^ shift.val := by
          intro hleft
          exact hbit ((routing_bit_zero_iff hshifted).mpr hleft)
        have hchild_mod :
            index.val % subtreeCapacity packing_factor child_depth =
              index.val %
                subtreeCapacity packing_factor (child_depth + 1) -
                  subtreeCapacity packing_factor child_depth := by
          rw [hchild_capacity, hparent_capacity, pow_succ]
          exact mod_child_eq_parent_sub_of_not_lt index.val
            (2 ^ shift.val) (Nat.two_pow_pos shift.val)
            (by simpa [pow_succ] using hroute)
        have hparent_route :
            subtreeCapacity packing_factor child_depth ≤
              index.val %
                subtreeCapacity packing_factor (child_depth + 1) := by
          rw [hchild_capacity, hparent_capacity]
          omega
        rw [hcapacity_succ] at hchild_mod hindex hparent_route hparent_mod_lt
        cases shape with
        | inl hempty => omega
        | inr hdense_shape =>
          have hleft_full : left_len =
              subtreeCapacity packing_factor child_depth := by
            by_cases hright_pos : 0 < right_len
            · exact hdense_shape.2 hright_pos
            · omega
          have hlocal :
              index.val % subtreeCapacity packing_factor child_depth ≤
                right_len := by
            rw [hchild_mod]
            omega
          cases hrecursive : Tree.with_updated_leaf ValueInst right index
              new_value new_depth with
          | fail e => rw [hrecursive] at hupdate; simp at hupdate
          | div => rw [hrecursive] at hupdate; simp at hupdate
          | ok result =>
            rw [hrecursive] at hupdate
            cases result with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hupdate
            | Ok new_right =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at hupdate
              subst updated
              have hrecursive_dense := ih new_depth right new_right child_depth
                right_len
                (by have := updateZbit_le_one right; omega)
                hnew_depth_val
                (UpdateReady.ofDense right_dense) hlocal hrecursive
              let new_right_len := updatedDenseLength packing_factor child_depth
                index right_len
              have hnode_dense : DenseTree packing_factor
                  (Tree.Node (Array.repeat 32#usize 0#u8) left new_right)
                  (child_depth + 1) (left_len + new_right_len) :=
                DenseTree.node packing_factor _ left new_right child_depth
                  left_len new_right_len left_dense hrecursive_dense
                  hdense_shape.1 (by intro; exact hleft_full)
              have hlength :
                  updatedDenseLength packing_factor (child_depth + 1) index
                      (left_len + right_len) = left_len + new_right_len := by
                unfold new_right_len
                unfold updatedDenseLength
                rw [hchild_mod, hcapacity_succ, hleft_full]
                split <;> split <;> omega
              rw [hlength]
              exact hnode_dense
    | zero packing_factor zero_depth =>
      unfold Tree.with_updated_leaf at hupdate
      have hdepth_eq : zero_depth = depth := by scalar_tac
      subst zero_depth
      rw [if_pos rfl] at hupdate
      by_cases hdepth_zero : depth = 0#usize
      · rw [if_pos hdepth_zero] at hupdate
        subst depth
        cases packing_factor with
        | none =>
          have hfactor := hlayout.opt_packing_factor_eq
          rw [hfactor] at hupdate
          simp [core.option.Option.is_some, Tree.leaf, milhouse.leaf.Leaf.new,
            milhouse.leaf.Leaf.with_hash,
            alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
          subst updated
          have hmod : index.val % 1 = 0 := Nat.mod_one index.val
          simpa [updatedDenseLength, subtreeCapacity, leafCapacity, hmod] using
            (DenseTree.leaf
              ({ hash := Array.repeat 32#usize 0#u8, value := new_value } :
                milhouse.leaf.Leaf T))
        | some factor =>
          have hfactor := hlayout.opt_packing_factor_eq
          rw [hfactor] at hupdate
          simp only [core.option.Option.is_some] at hupdate
          cases hsingle : packed_leaf.PackedLeaf.single
              ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst
              new_value with
          | fail e => rw [hsingle] at hupdate; simp at hupdate
          | div => rw [hsingle] at hupdate; simp at hupdate
          | ok new_leaf =>
            rw [hsingle] at hupdate
            simp [triomphe.arc.Arc.new] at hupdate
            subst updated
            obtain ⟨canonical_leaf, hcanonical, hcanonical_dense⟩ :=
              packedLeaf_single_preserves_dense ValueInst hlayout new_value
            rw [hsingle] at hcanonical
            simp at hcanonical
            subst canonical_leaf
            have hfactor_pos : 0 < factor.val := by
              simpa [leafCapacity] using hlayout.leafCapacity_pos
            have hmod : index.val % factor.val = 0 := by
              simpa [subtreeCapacity, leafCapacity] using hindex
            simpa [updatedDenseLength, subtreeCapacity, leafCapacity, hmod,
              hfactor_pos] using hcanonical_dense
      · rw [if_neg hdepth_zero] at hupdate
        simp [Tree.zero, triomphe.arc.Arc.new,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          alloy_primitives.bits.fixed.FixedBytes.ZERO, Tree.node,
          lock_api.rwlock.RwLock.new,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hupdate
        simp only [result_bind_eq_ok_iff] at hupdate
        obtain ⟨child_depth, hchild_depth, hrecursive⟩ := hupdate
        have hchild_depth_val := usize_sub_one_val hchild_depth
        let empty_node : Tree T := Tree.Node (Array.repeat 32#usize 0#u8)
          (@Tree.Zero T child_depth) (@Tree.Zero T child_depth)
        have hempty_ready : UpdateReady packing_factor empty_node depth.val 0 := by
          have hready := UpdateReady.node packing_factor
            (Array.repeat 32#usize 0#u8) (@Tree.Zero T child_depth)
            (@Tree.Zero T child_depth) child_depth.val 0 0
            (@DenseTree.zero T packing_factor child_depth)
            (@DenseTree.zero T packing_factor child_depth)
            (Or.inl ⟨rfl, rfl⟩)
          simpa [empty_node, hchild_depth_val] using hready
        have hrecursive_measure :
            2 * depth.val + updateZbit empty_node ≤ n := by
          simp [empty_node, updateZbit] at hmeasure ⊢
          omega
        exact ih depth empty_node updated depth.val 0
          hrecursive_measure rfl hempty_ready hindex
          hrecursive

/-- A successful single-value update preserves density. It increases the
    logical length exactly at the current dense right edge when the subtree is
    not already full. -/
theorem with_updated_leaf_preserves_dense {T : Type}
    (ValueInst : Value T) {packing_factor : Option Std.Usize}
    {packing_depth depth : Std.Usize} {self updated : Tree T} {len : Nat}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor self depth.val len)
    (index : Std.Usize) (hindex : index.val ≤ len) (new_value : T)
    (hupdate : Tree.with_updated_leaf ValueInst self index new_value depth =
      ok (core.result.Result.Ok updated)) :
    DenseTree packing_factor updated depth.val
      (updatedDenseLength packing_factor depth.val index len) := by
  apply with_updated_leaf_preserves_dense_aux ValueInst hlayout index new_value
    (2 * depth.val + updateZbit self) depth self updated depth.val len
    (Nat.le_refl _) rfl (UpdateReady.ofDense hdense)
  by_cases hindex_lt : index.val <
      subtreeCapacity packing_factor depth.val
  · simpa [Nat.mod_eq_of_lt hindex_lt] using hindex
  · have hcapacity := hdense.length_le_capacity
    have hindex_eq : index.val = subtreeCapacity packing_factor depth.val := by
      omega
    rw [hindex_eq, Nat.mod_self]
    omega
  exact hupdate

/-! ## Bulk update preservation -/

/-- Setting a single clear bit is addition: `a ||| 2^s = a + 2^s` when `a`
    is aligned past bit `s`. Bridges the translated `prefix | (1 << shift)`
    to the arithmetic form used by the dense split. -/
private theorem or_two_pow_aligned {a s : Nat} (h : a % 2 ^ (s + 1) = 0) :
    a ||| 2 ^ s = a + 2 ^ s := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  apply Nat.eq_of_testBit_eq
  intro i
  have hsum : 2 ^ (s + 1) * q + 2 ^ s = (2 * q + 1) <<< s := by
    rw [Nat.shiftLeft_eq]
    ring
  have hshift : 2 ^ (s + 1) * q = q <<< (s + 1) := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hsum, hshift]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i s with hlt | heq | hgt
  · have h1 : ¬ (s + 1 ≤ i) := by omega
    have h2 : ¬ (s ≤ i) := by omega
    have h3 : ¬ (s = i) := by omega
    simp [h1, h2, h3]
  · subst heq
    have h1 : ¬ (i + 1 ≤ i) := by omega
    simp [h1, Nat.testBit_zero]
    try omega
  · have h1 : s + 1 ≤ i := by omega
    have h2 : s ≤ i := by omega
    have h3 : ¬ (s = i) := by omega
    simp only [h1, h2, h3, decide_true, decide_false, Bool.true_and,
      Bool.or_false]
    obtain ⟨j, hj⟩ : ∃ j, i - s = j + 1 := ⟨i - s - 1, by omega⟩
    rw [hj, Nat.testBit_add_one]
    have hdiv : (2 * q + 1) / 2 = q := by omega
    rw [hdiv]
    congr 1
    omega

/-- Bitwise-or on `Usize` is bitwise-or of the values. -/
private theorem usize_or_val (x y : Std.Usize) :
    (x ||| y).val = x.val ||| y.val := by
  show (UScalar.or x y).val = x.val ||| y.val
  simp only [UScalar.or, UScalar.val]
  simp [BitVec.toNat_or]

/-- Alignment descends to the half capacity. -/
private theorem mod_half_eq_zero {p h : Nat} (hp : p % (h * 2) = 0) :
    p % h = 0 :=
  Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans ⟨2, rfl⟩ (Nat.dvd_of_mod_eq_zero hp))

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

/-- One unfolding of the translated packed-leaf update loop. -/
private theorem update_loop_step {T U : Type}
    (thi : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (mapInst : update_map.UpdateMap U T) (updates : U)
    (updated : packed_leaf.PackedLeaf T) (factor end1 index : Std.Usize) :
    packed_leaf.PackedLeaf.update_loop thi cloneInst mapInst updates updated
      factor end1 index =
      match packed_leaf.PackedLeaf.update_loop.body thi cloneInst mapInst
          updates factor end1 updated index with
      | ok (.cont (u, i)) => packed_leaf.PackedLeaf.update_loop thi cloneInst
          mapInst updates u factor end1 i
      | ok (.done b) => ok b
      | fail e => fail e
      | div => div := by
  conv_lhs => unfold packed_leaf.PackedLeaf.update_loop
  conv_lhs => unfold Aeneas.Std.loop
  cases hb : packed_leaf.PackedLeaf.update_loop.body thi cloneInst mapInst
      updates factor end1 updated index with
  | fail e => simp [hb]
  | div => simp [hb]
  | ok cf =>
    cases cf with
    | cont x =>
      obtain ⟨u, i⟩ := x
      simp [hb]
      rfl
    | done b => simp [hb]

/-- Length of the packed-leaf bulk-update loop result. With a `get` that
    reflects the logical update set and a dense update window, a successful
    loop drives the value count from the old to the new dense length. The
    length invariant is carried as a three-way disjunction on the scan
    position. -/
private theorem update_loop_length {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {has_update : Nat → Prop}
    (hget : ∀ (i : Std.Usize) (found : Option T),
      mapInst.get updates i = ok found →
      (found.isSome = true ↔ has_update i.val))
    {factor end1 : Std.Usize} {window old_len new_len : Nat}
    (hend : end1.val = window + factor.val)
    (halign : window % factor.val = 0)
    (hfactor_pos : 0 < factor.val)
    (hmono : old_len ≤ new_len)
    (hcomplete : ∀ i, old_len ≤ i → i < new_len → has_update (window + i))
    (hbounded : ∀ i, i < factor.val → has_update (window + i) → i < new_len)
    (hnew_cap : new_len ≤ factor.val) :
    ∀ (fuel : Nat) (updated : packed_leaf.PackedLeaf T) (index : Std.Usize)
      (result : packed_leaf.PackedLeaf T),
      end1.val - index.val ≤ fuel →
      window ≤ index.val → index.val ≤ end1.val →
      ((index.val - window ≤ old_len ∧
          updated.values.val.length = old_len) ∨
        (old_len ≤ index.val - window ∧ index.val - window ≤ new_len ∧
          updated.values.val.length = index.val - window) ∨
        (new_len ≤ index.val - window ∧
          updated.values.val.length = new_len)) →
      packed_leaf.PackedLeaf.update_loop thi cloneInst mapInst updates
        updated factor end1 index = ok (core.result.Result.Ok result) →
      result.values.val.length = new_len := by
  intro fuel
  induction fuel with
  | zero =>
    intro updated index result hfuel hlo hhi hlen hloop
    have hstop : ¬ index < end1 := by scalar_tac
    rw [update_loop_step] at hloop
    unfold packed_leaf.PackedLeaf.update_loop.body at hloop
    rw [if_neg hstop] at hloop
    simp at hloop
    subst hloop
    omega
  | succ fuel ihfuel =>
    intro updated index result hfuel hlo hhi hlen hloop
    rw [update_loop_step] at hloop
    by_cases hlt : index < end1
    case neg =>
      unfold packed_leaf.PackedLeaf.update_loop.body at hloop
      rw [if_neg hlt] at hloop
      simp at hloop
      subst hloop
      have hk : index.val - window = factor.val := by scalar_tac
      omega
    case pos =>
    have hklt : index.val - window < factor.val := by scalar_tac
    cases hb : packed_leaf.PackedLeaf.update_loop.body thi cloneInst mapInst
        updates factor end1 updated index with
    | fail e => rw [hb] at hloop; simp at hloop
    | div => rw [hb] at hloop; simp at hloop
    | ok cf =>
    rw [hb] at hloop
    unfold packed_leaf.PackedLeaf.update_loop.body at hb
    rw [if_pos hlt] at hb
    rw [result_bind_eq_ok_iff] at hb
    obtain ⟨found, hgeteq, hb⟩ := hb
    have hiff := hget index found hgeteq
    cases found with
    | none =>
      have hno_update : ¬ has_update index.val := by
        intro hup
        simpa using hiff.mpr hup
      rw [result_bind_eq_ok_iff] at hb
      obtain ⟨index1, hplus, hb⟩ := hb
      have hplus_val := usize_add_val hplus
      simp at hplus_val
      simp at hb
      subst hb
      simp at hloop
      have hnot_pending :
          ¬ (old_len ≤ index.val - window ∧
              index.val - window < new_len) := by
        rintro ⟨h1, h2⟩
        refine hno_update ?_
        have hcov := hcomplete (index.val - window) h1 h2
        have hidx : window + (index.val - window) = index.val := by omega
        rwa [hidx] at hcov
      refine ihfuel updated index1 result (by scalar_tac) (by scalar_tac)
        (by scalar_tac) (by omega) hloop
    | some value =>
      have hup : has_update index.val := hiff.mp (by simp)
      have hup_bound : index.val - window < new_len := by
        refine hbounded (index.val - window) hklt ?_
        have hidx : window + (index.val - window) = index.val := by omega
        rwa [hidx]
      rw [result_bind_eq_ok_iff] at hb
      obtain ⟨sub, hrem, hb⟩ := hb
      have hsub_val : sub.val = index.val - window := by
        obtain ⟨r, hr, hrval⟩ := usize_rem_succeeds index hfactor_pos
        rw [hrem] at hr
        cases hr
        have hidx : index.val = window + (index.val - window) := by omega
        rw [hidx, Nat.add_mod, halign, Nat.zero_add,
          Nat.mod_eq_of_lt (Nat.mod_lt _ hfactor_pos),
          Nat.mod_eq_of_lt hklt] at hrval
        omega
      rw [result_bind_eq_ok_iff] at hb
      obtain ⟨cloned, hclone, hb⟩ := hb
      rw [result_bind_eq_ok_iff] at hb
      obtain ⟨⟨r, updated1⟩, hins, hb⟩ := hb
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hb
        subst hb
        simp at hloop
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hb
        rw [result_bind_eq_ok_iff] at hb
        obtain ⟨index1, hplus, hb⟩ := hb
        have hplus_val := usize_add_val hplus
        simp at hplus_val
        simp at hb
        subst hb
        simp at hloop
        obtain ⟨hlen1, hsub_le⟩ := packedLeaf_insert_mut_length hins
        rw [hsub_val] at hlen1 hsub_le
        refine ihfuel updated1 index1 result (by scalar_tac) (by scalar_tac)
          (by scalar_tac) ?_ hloop
        split at hlen1 <;> omega

/-- A successful bulk update of a `Leaf` returns a `Leaf`. -/
private theorem with_updated_leaves_leaf_shape {T U : Type}
    {ValueInst : Value T} {mapInst : update_map.UpdateMap U T} {updates : U}
    {l : leaf.Leaf T} {prefix1 depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap
      (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    {updated : triomphe.arc.Arc (Tree T)}
    (hupdate : Tree.with_updated_leaves ValueInst mapInst (Tree.Leaf l)
      updates prefix1 depth hashes = ok (core.result.Result.Ok updated)) :
    ∃ leaf', updated = Tree.Leaf leaf' := by
  unfold Tree.with_updated_leaves at hupdate
  rw [result_bind_eq_ok_iff] at hupdate
  obtain ⟨opt, hopt, hupdate⟩ := hupdate
  rw [result_bind_eq_ok_iff] at hupdate
  obtain ⟨hash, hhash, hupdate⟩ := hupdate
  by_cases hdepth : depth = 0#usize
  · subst hdepth
    simp only [↓reduceIte] at hupdate
    rw [result_bind_eq_ok_iff] at hupdate
    obtain ⟨found, hfound, hupdate⟩ := hupdate
    rw [result_bind_eq_ok_iff] at hupdate
    obtain ⟨cloned, hcloned, hupdate⟩ := hupdate
    cases cloned with
    | none =>
      simp [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hupdate
    | some value =>
      simp [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, Tree.leaf_with_hash,
        leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new,
        triomphe.arc.Arc.new] at hupdate
      exact ⟨_, hupdate.symm⟩
  · simp [hdepth] at hupdate

/-- A successful bulk update of a packed leaf yields the window's new dense
    length, provided `get` reflects the logical update set on the window. -/
private theorem packedLeaf_update_length {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {has_update : Nat → Prop}
    (hget : ∀ (i : Std.Usize) (found : Option T),
      mapInst.get updates i = ok found →
      (found.isSome = true ↔ has_update i.val))
    {pl result : packed_leaf.PackedLeaf T} {prefix1 : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    {factor : Std.Usize} {new_len : Nat}
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (hfactor_pos : 0 < factor.val)
    (halign : prefix1.val % factor.val = 0)
    (hmono : pl.values.val.length ≤ new_len)
    (hcomplete : ∀ i, pl.values.val.length ≤ i → i < new_len →
      has_update (prefix1.val + i))
    (hbounded : ∀ i, i < factor.val → has_update (prefix1.val + i) →
      i < new_len)
    (hnew_cap : new_len ≤ factor.val)
    (hupdate : packed_leaf.PackedLeaf.update thi cloneInst mapInst pl prefix1
      hash updates = ok (core.result.Result.Ok result)) :
    result.values.val.length = new_len := by
  unfold packed_leaf.PackedLeaf.update at hupdate
  simp only [lock_api.rwlock.RwLock.new, bind_tc_ok] at hupdate
  rw [result_bind_eq_ok_iff] at hupdate
  obtain ⟨values, hvalues, hupdate⟩ := hupdate
  have hvalues_len : values.val.length = pl.values.val.length :=
    Aeneas.Std.Slice.clone_length hvalues
  rw [hfactor] at hupdate
  simp only [bind_tc_ok] at hupdate
  rw [result_bind_eq_ok_iff] at hupdate
  obtain ⟨end1, hend1, hupdate⟩ := hupdate
  have hend1_val := usize_add_val hend1
  refine update_loop_length hget hend1_val halign hfactor_pos hmono
    hcomplete hbounded hnew_cap (end1.val - prefix1.val)
    { hash := hash, values := values } prefix1 result (Nat.le_refl _)
    (Nat.le_refl _) (by omega) ?_ hupdate
  left
  exact ⟨by omega, hvalues_len⟩

/-- Bulk-update preservation, by induction on depth with the `Zero`
    expansion tie-breaker. The update window premises are stated relative to
    the subtree's aligned prefix. -/
private theorem with_updated_leaves_preserves_dense_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {packing_factor : Option Std.Usize} {packing_depth : Std.Usize}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    {has_update : Nat → Prop}
    (hget : ∀ (i : Std.Usize) (found : Option T),
      mapInst.get updates i = ok found →
      (found.isSome = true ↔ has_update i.val))
    (hrange : ∀ (lo hi : Std.Usize) (r : Bool),
      mapInst.has_any_in_range updates lo hi = ok r →
      (r = true ↔ ∃ j, lo.val ≤ j ∧ j < hi.val ∧ has_update j))
    (hashes : Option (alloc.collections.btree.map.BTreeMap
      (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)) :
    ∀ (n : Nat) (depth prefix1 : Std.Usize) (self : Tree T)
      (updated : triomphe.arc.Arc (Tree T)) (tree_depth old_len new_len : Nat),
      2 * depth.val + updateZbit self ≤ n →
      depth.val = tree_depth →
      UpdateReady packing_factor self tree_depth old_len →
      prefix1.val % subtreeCapacity packing_factor tree_depth = 0 →
      old_len ≤ new_len →
      0 < new_len →
      new_len ≤ subtreeCapacity packing_factor tree_depth →
      (∀ i, old_len ≤ i → i < new_len → has_update (prefix1.val + i)) →
      (∀ i, i < subtreeCapacity packing_factor tree_depth →
        has_update (prefix1.val + i) → i < new_len) →
      Tree.with_updated_leaves ValueInst mapInst self updates prefix1 depth
        hashes = ok (core.result.Result.Ok updated) →
      DenseTree packing_factor updated tree_depth new_len := by
  have leaf_case : ∀ (l : leaf.Leaf T) (prefix1 depth : Std.Usize)
      (updated : triomphe.arc.Arc (Tree T)) (new_len : Nat),
      0 < new_len → new_len ≤ subtreeCapacity none 0 →
      Tree.with_updated_leaves ValueInst mapInst (Tree.Leaf l) updates prefix1
        depth hashes = ok (core.result.Result.Ok updated) →
      DenseTree none updated 0 new_len := by
    intro l prefix1 depth updated new_len hpos hcap hupdate
    obtain ⟨leaf', rfl⟩ := with_updated_leaves_leaf_shape hupdate
    have hone : subtreeCapacity none 0 = 1 := by
      simp [subtreeCapacity, leafCapacity]
    have hnew_one : new_len = 1 := by omega
    rw [hnew_one]
    exact DenseTree.leaf leaf'
  intro n
  induction n with
  | zero =>
    intro depth prefix1 self updated tree_depth old_len new_len hmeasure
      hdepth_eq hready halign hmono hpos hcap hcomplete hbounded hupdate
    cases hready with
    | zero packing_factor zero_depth => simp [updateZbit] at hmeasure
    | leaf l =>
      exact leaf_case l prefix1 depth updated new_len hpos hcap hupdate
    | packed factor pl hnonempty hfit =>
      have hdepth0 : depth = 0#usize := by scalar_tac
      subst hdepth0
      unfold Tree.with_updated_leaves at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨opt, hopt, hupdate⟩ := hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨hash, hhash, hupdate⟩ := hupdate
      simp only [↓reduceIte] at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨res, hres, hupdate⟩ := hupdate
      cases res with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hupdate
      | Ok pl' =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          triomphe.arc.Arc.new] at hupdate
        subst hupdate
        have hfactor := hlayout.tree_hash_packing_factor_eq
        have hfactor_pos : 0 < factor.val := by
          simpa [leafCapacity] using hlayout.leafCapacity_pos
        have hcapf : subtreeCapacity (some factor) 0 = factor.val := by
          simp [subtreeCapacity, leafCapacity]
        have hlen := packedLeaf_update_length hget hfactor hfactor_pos
          (by rwa [hcapf] at halign) hmono hcomplete
          (by rw [← hcapf]; exact hbounded) (by omega) hres
        rw [← hlen] at hpos hcap ⊢
        exact DenseTree.packed factor pl' hpos (by rwa [hcapf] at hcap)
    | node packing_factor rl left right child_depth left_len right_len
        left_dense right_dense shape =>
      simp [updateZbit] at hmeasure
      omega
  | succ n ih =>
    intro depth prefix1 self updated tree_depth old_len new_len hmeasure
      hdepth_eq hready halign hmono hpos hcap hcomplete hbounded hupdate
    cases hready with
    | leaf l =>
      exact leaf_case l prefix1 depth updated new_len hpos hcap hupdate
    | packed factor pl hnonempty hfit =>
      have hdepth0 : depth = 0#usize := by scalar_tac
      subst hdepth0
      unfold Tree.with_updated_leaves at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨opt, hopt, hupdate⟩ := hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨hash, hhash, hupdate⟩ := hupdate
      simp only [↓reduceIte] at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨res, hres, hupdate⟩ := hupdate
      cases res with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hupdate
      | Ok pl' =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          triomphe.arc.Arc.new] at hupdate
        subst hupdate
        have hfactor := hlayout.tree_hash_packing_factor_eq
        have hfactor_pos : 0 < factor.val := by
          simpa [leafCapacity] using hlayout.leafCapacity_pos
        have hcapf : subtreeCapacity (some factor) 0 = factor.val := by
          simp [subtreeCapacity, leafCapacity]
        have hlen := packedLeaf_update_length hget hfactor hfactor_pos
          (by rwa [hcapf] at halign) hmono hcomplete
          (by rw [← hcapf]; exact hbounded) (by omega) hres
        rw [← hlen] at hpos hcap ⊢
        exact DenseTree.packed factor pl' hpos (by rwa [hcapf] at hcap)
    | zero packing_factor zero_depth =>
      have hz : zero_depth = depth := by scalar_tac
      subst hz
      unfold Tree.with_updated_leaves at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨opt, hopt, hupdate⟩ := hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨hash, hhash, hupdate⟩ := hupdate
      simp only [↓reduceIte] at hupdate
      by_cases hdepth0 : zero_depth = 0#usize
      · subst hdepth0
        simp only [↓reduceIte] at hupdate
        have h0v : (0#usize).val = 0 := by simp
        simp only [h0v] at halign hcap hbounded ⊢
        rw [hlayout.opt_packing_factor_eq] at hupdate
        simp only [bind_tc_ok] at hupdate
        cases hpf : packing_factor with
        | some factor =>
          rw [hpf] at hupdate
          simp only [core.option.Option.is_some, Option.isSome_some,
            if_true] at hupdate
          rw [result_bind_eq_ok_iff] at hupdate
          obtain ⟨pl0, hpl0, hupdate⟩ := hupdate
          rw [result_bind_eq_ok_iff] at hupdate
          obtain ⟨res, hres, hupdate⟩ := hupdate
          cases res with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok pl' =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              triomphe.arc.Arc.new] at hupdate
            subst hupdate
            rw [hpf] at hlayout halign hcap hbounded
            have hfactor := hlayout.tree_hash_packing_factor_eq
            have hpl0_len : pl0.values.val.length = 0 := by
              unfold packed_leaf.PackedLeaf.empty at hpl0
              rw [hfactor] at hpl0
              simp [alloy_primitives.bits.fixed.FixedBytes.ZERO,
                lock_api.rwlock.RwLock.new] at hpl0
              subst hpl0
              simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
            have hfactor_pos : 0 < factor.val := by
              simpa [leafCapacity] using hlayout.leafCapacity_pos
            have hcapf : subtreeCapacity (some factor) 0 = factor.val := by
              simp [subtreeCapacity, leafCapacity]
            have hlen := packedLeaf_update_length hget hfactor hfactor_pos
              (by rwa [hcapf] at halign) (by omega)
              (by rw [hpl0_len]; intro j h1 h2
                  exact hcomplete j (by omega) h2)
              (by rw [← hcapf]; exact hbounded) (by omega) hres
            rw [← hlen] at hpos hcap ⊢
            exact DenseTree.packed factor pl' hpos (by rwa [hcapf] at hcap)
        | none =>
          rw [hpf] at hupdate
          simp only [core.option.Option.is_some, Option.isSome_none,
            Bool.false_eq_true, if_false] at hupdate
          rw [result_bind_eq_ok_iff] at hupdate
          obtain ⟨found, hfound, hupdate⟩ := hupdate
          rw [result_bind_eq_ok_iff] at hupdate
          obtain ⟨cloned, hcloned, hupdate⟩ := hupdate
          cases cloned with
          | none =>
            simp [core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | some value =>
            simp [core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch, Tree.leaf_with_hash,
              leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new,
              triomphe.arc.Arc.new] at hupdate
            subst hupdate
            rw [hpf] at hcap
            have hone : subtreeCapacity none 0 = 1 := by
              simp [subtreeCapacity, leafCapacity]
            have hnew_one : new_len = 1 := by omega
            rw [hnew_one]
            exact DenseTree.leaf _
      · simp only [if_neg hdepth0] at hupdate
        rw [result_bind_eq_ok_iff] at hupdate
        obtain ⟨i, hi, hupdate⟩ := hupdate
        have hi_val := usize_sub_one_val hi
        simp only [Tree.zero, triomphe.arc.Arc.new,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone, Tree.node,
          lock_api.rwlock.RwLock.new,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          bind_tc_ok] at hupdate
        refine ih zero_depth prefix1
          (Tree.Node hash (Tree.Zero i) (Tree.Zero i)) updated
          zero_depth.val 0 new_len ?_ rfl ?_ halign (by omega) hpos hcap
          (by intro j h1 h2; exact hcomplete j (by omega) h2) hbounded hupdate
        · simp only [updateZbit] at hmeasure ⊢
          omega
        · have hnode := UpdateReady.node (T := T) packing_factor hash
            (Tree.Zero i) (Tree.Zero i) i.val 0 0
            (DenseTree.zero packing_factor i)
            (DenseTree.zero packing_factor i) (Or.inl ⟨rfl, rfl⟩)
          have htd : zero_depth.val = i.val + 1 := by omega
          rw [htd]
          simpa using hnode
    | node packing_factor rl left right child_depth left_len right_len
        left_dense right_dense shape =>
      unfold Tree.with_updated_leaves at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨opt, hopt, hupdate⟩ := hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨hash, hhash, hupdate⟩ := hupdate
      have hdepth_pos : depth > 0#usize := by scalar_tac
      simp only [if_pos hdepth_pos] at hupdate
      rw [hlayout.opt_packing_depth_eq] at hupdate
      have hunwrap := hlayout.unwrap_opt_packing_depth_eq
      simp only [hunwrap, lift, bind_tc_ok,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
        triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨new_depth, hnew_depth, hupdate⟩ := hupdate
      have hnd_val := usize_sub_one_val hnew_depth
      have hnd_depth : new_depth.val = child_depth := by omega
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨i, hi, hupdate⟩ := hupdate
      have hi_val := usize_add_val hi
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨i1, hi1, hupdate⟩ := hupdate
      have hi1_val := usize_shift_left_one_val hi1
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨i2, hi2, hupdate⟩ := hupdate
      have hi2_val := usize_add_val hi2
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨i3, hi3, hupdate⟩ := hupdate
      have hi3_val := usize_shift_left_one_val hi3
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨rse, hrse, hupdate⟩ := hupdate
      have hrse_val := usize_add_val hrse
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨bl, hbl, hupdate⟩ := hupdate
      rw [result_bind_eq_ok_iff] at hupdate
      obtain ⟨br, hbr, hupdate⟩ := hupdate
      have hchild_capacity :
          subtreeCapacity packing_factor child_depth = 2 ^ i.val := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      have hparent_capacity :
          subtreeCapacity packing_factor (child_depth + 1) =
            2 ^ (i.val + 1) := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      have hcap_succ : subtreeCapacity packing_factor (child_depth + 1) =
          subtreeCapacity packing_factor child_depth * 2 := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
      have hchild_cap_pos := hlayout.subtreeCapacity_pos child_depth
      have hleft_bound := left_dense.length_le_capacity
      have hright_bound := right_dense.length_le_capacity
      have halign' : prefix1.val % (2 ^ (i.val + 1)) = 0 := by
        rw [← hparent_capacity]
        exact halign
      have hor : prefix1.val ||| 2 ^ i.val = prefix1.val + 2 ^ i.val :=
        or_two_pow_aligned halign'
      have hrp_val : (prefix1 ||| i1).val = prefix1.val + 2 ^ i.val := by
        rw [usize_or_val, hi1_val, hor]
      have hrse_val' : rse.val = prefix1.val + 2 ^ (i.val + 1) := by
        rw [hrse_val, hi3_val]
        congr 2
        omega
      have hbl_iff := hrange _ _ _ hbl
      have hbr_iff := hrange _ _ _ hbr
      have hleft_window : bl = true ↔
          ∃ off, off < subtreeCapacity packing_factor child_depth ∧
            has_update (prefix1.val + off) := by
        rw [hbl_iff, hchild_capacity]
        constructor
        · rintro ⟨j, hj1, hj2, hj3⟩
          rw [hrp_val] at hj2
          refine ⟨j - prefix1.val, by omega, ?_⟩
          have hj : prefix1.val + (j - prefix1.val) = j := by omega
          rwa [hj]
        · rintro ⟨off, hoff1, hoff2⟩
          exact ⟨prefix1.val + off, by omega, by rw [hrp_val]; omega, hoff2⟩
      have hright_window : br = true ↔
          ∃ off, subtreeCapacity packing_factor child_depth ≤ off ∧
            off < subtreeCapacity packing_factor (child_depth + 1) ∧
            has_update (prefix1.val + off) := by
        rw [hbr_iff, hchild_capacity, hparent_capacity]
        constructor
        · rintro ⟨j, hj1, hj2, hj3⟩
          rw [hrp_val] at hj1
          rw [hrse_val'] at hj2
          refine ⟨j - prefix1.val, by omega, by omega, ?_⟩
          have hj : prefix1.val + (j - prefix1.val) = j := by omega
          rwa [hj]
        · rintro ⟨off, hoff1, hoff2, hoff3⟩
          exact ⟨prefix1.val + off, by rw [hrp_val]; omega,
            by rw [hrse_val']; omega, hoff3⟩
      obtain ⟨nlL, nlR, hnl_sum, hnlL_le, hnl_shape⟩ :
          ∃ nl nr, new_len = nl + nr ∧
            nl ≤ subtreeCapacity packing_factor child_depth ∧
            ((nr = 0 ∧ nl = new_len) ∨
              nl = subtreeCapacity packing_factor child_depth) := by
        by_cases hle : new_len ≤ subtreeCapacity packing_factor child_depth
        · exact ⟨new_len, 0, by omega, hle, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨subtreeCapacity packing_factor child_depth,
            new_len - subtreeCapacity packing_factor child_depth, by omega,
            Nat.le_refl _, Or.inr rfl⟩
      have hold_split :
          left_len ≤ subtreeCapacity packing_factor child_depth ∧
            (right_len = 0 ∨
              left_len = subtreeCapacity packing_factor child_depth) := by
        rcases shape with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by omega, Or.inl h2⟩
        · by_cases hr : 0 < right_len
          · exact ⟨hleft_bound, Or.inr (h2 hr)⟩
          · exact ⟨hleft_bound, Or.inl (by omega)⟩
      have hside_full : 0 < nlR →
          nlL = subtreeCapacity packing_factor child_depth := by
        rcases hnl_shape with ⟨h3, h4⟩ | h3 <;> omega
      have hnlL_pos : 0 < nlL := by
        rcases hnl_shape with ⟨h3, h4⟩ | h3 <;> omega
      have hL_old_le : left_len ≤ nlL := by
        rcases hnl_shape with ⟨h3, h4⟩ | h3 <;>
          rcases hold_split.2 with h5 | h5 <;> omega
      have hL_complete : ∀ off, left_len ≤ off → off < nlL →
          has_update (prefix1.val + off) := by
        intro off h1 h2
        rcases hold_split.2 with h3 | h3
        · exact hcomplete off (by omega) (by omega)
        · omega
      have hL_bounded : ∀ off,
          off < subtreeCapacity packing_factor child_depth →
          has_update (prefix1.val + off) → off < nlL := by
        intro off h1 h2
        have hb := hbounded off (by omega) h2
        rcases hnl_shape with ⟨h3, h4⟩ | h3 <;> omega
      have hR_old_le : right_len ≤ nlR := by
        rcases hold_split.2 with h3 | h3
        · omega
        · rcases hnl_shape with ⟨h4, h5⟩ | h4 <;> omega
      have hR_complete : ∀ off, right_len ≤ off → off < nlR →
          has_update ((prefix1 ||| i1).val + off) := by
        intro off h1 h2
        have hj := hcomplete
          (subtreeCapacity packing_factor child_depth + off)
          (by omega) (by rcases hnl_shape with ⟨h3, h4⟩ | h3 <;> omega)
        have heq : prefix1.val +
            (subtreeCapacity packing_factor child_depth + off) =
            (prefix1 ||| i1).val + off := by
          rw [hrp_val, hchild_capacity]
          omega
        rwa [heq] at hj
      have hR_bounded : ∀ off,
          off < subtreeCapacity packing_factor child_depth →
          has_update ((prefix1 ||| i1).val + off) → off < nlR := by
        intro off h1 h2
        have heq : (prefix1 ||| i1).val + off =
            prefix1.val +
              (subtreeCapacity packing_factor child_depth + off) := by
          rw [hrp_val, hchild_capacity]
          omega
        rw [heq] at h2
        have hb := hbounded
          (subtreeCapacity packing_factor child_depth + off)
          (by omega) h2
        rcases hnl_shape with ⟨h3, h4⟩ | h3 <;> omega
      have hR_cap : nlR ≤ subtreeCapacity packing_factor child_depth := by
        rcases hnl_shape with ⟨h3, h4⟩ | h3 <;> omega
      have halign_left :
          prefix1.val % subtreeCapacity packing_factor child_depth = 0 := by
        apply mod_half_eq_zero
        rwa [← hcap_succ]
      have halign_right : (prefix1 ||| i1).val %
          subtreeCapacity packing_factor child_depth = 0 := by
        rw [hrp_val, ← hchild_capacity, Nat.add_mod_right]
        exact halign_left
      have hmeasure_child : ∀ t : Tree T,
          2 * new_depth.val + updateZbit t ≤ n := by
        intro t
        have := updateZbit_le_one t
        simp only [updateZbit] at hmeasure
        omega
      cases bl with
      | false =>
        have hno_left : ¬ ∃ off,
            off < subtreeCapacity packing_factor child_depth ∧
            has_update (prefix1.val + off) := by
          intro hex
          simpa using hleft_window.mpr hex
        have hnlL_eq : nlL = left_len := by
          by_contra hne
          have hlt : left_len < nlL := by omega
          exact hno_left ⟨left_len, by omega,
            hL_complete left_len (Nat.le_refl _) hlt⟩
        cases br with
        | false => simp at hupdate
        | true =>
          simp only [Bool.false_eq_true, if_false, if_true] at hupdate
          rw [result_bind_eq_ok_iff] at hupdate
          obtain ⟨r, hr, hupdate⟩ := hupdate
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok new_right =>
            simp [core.result.Result.Insts.CoreOpsTry.branch, Tree.node,
              lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
            subst hupdate
            have hR_pos : 0 < nlR := by
              obtain ⟨off, hoff1, hoff2, hoff3⟩ := hright_window.mp rfl
              have heq : prefix1.val + off =
                  (prefix1 ||| i1).val +
                    (off - subtreeCapacity packing_factor child_depth) := by
                rw [hrp_val, ← hchild_capacity]
                omega
              rw [heq] at hoff3
              have := hR_bounded
                (off - subtreeCapacity packing_factor child_depth)
                (by omega) hoff3
              omega
            have hdense_right := ih new_depth (prefix1 ||| i1) right
              new_right child_depth right_len nlR (hmeasure_child right)
              hnd_depth (UpdateReady.ofDense right_dense) halign_right
              hR_old_le hR_pos hR_cap hR_complete hR_bounded hr
            rw [hnl_sum]
            exact DenseTree.node packing_factor hash left new_right
              child_depth nlL nlR (hnlL_eq ▸ left_dense) hdense_right
              hnlL_pos hside_full
      | true =>
        simp only [if_true] at hupdate
        rw [result_bind_eq_ok_iff] at hupdate
        obtain ⟨r, hr, hupdate⟩ := hupdate
        cases r with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | Ok new_left =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok] at hupdate
          have hdense_left := ih new_depth prefix1 left new_left child_depth
            left_len nlL (hmeasure_child left) hnd_depth
            (UpdateReady.ofDense left_dense) halign_left hL_old_le hnlL_pos
            hnlL_le hL_complete hL_bounded hr
          cases br with
          | false =>
            have hno_right : ¬ ∃ off,
                subtreeCapacity packing_factor child_depth ≤ off ∧
                off < subtreeCapacity packing_factor (child_depth + 1) ∧
                has_update (prefix1.val + off) := by
              intro hex
              simpa using hright_window.mpr hex
            have hnlR_eq : nlR = right_len := by
              by_contra hne
              have hlt : right_len < nlR := by omega
              have hup := hR_complete right_len (Nat.le_refl _) hlt
              have heq : (prefix1 ||| i1).val + right_len =
                  prefix1.val +
                    (subtreeCapacity packing_factor child_depth +
                      right_len) := by
                rw [hrp_val, hchild_capacity]
                omega
              rw [heq] at hup
              exact hno_right
                ⟨subtreeCapacity packing_factor child_depth + right_len,
                  by omega, by omega, hup⟩
            simp only [Bool.false_eq_true, if_false] at hupdate
            simp [Tree.node, lock_api.rwlock.RwLock.new,
              triomphe.arc.Arc.new] at hupdate
            subst hupdate
            rw [hnl_sum]
            exact DenseTree.node packing_factor hash new_left right
              child_depth nlL nlR hdense_left (hnlR_eq ▸ right_dense)
              hnlL_pos hside_full
          | true =>
            simp only [if_true] at hupdate
            rw [result_bind_eq_ok_iff] at hupdate
            obtain ⟨r1, hr1, hupdate⟩ := hupdate
            cases r1 with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hupdate
            | Ok new_right =>
              simp [Tree.node,
                lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
              subst hupdate
              have hR_pos : 0 < nlR := by
                obtain ⟨off, hoff1, hoff2, hoff3⟩ := hright_window.mp rfl
                have heq : prefix1.val + off =
                    (prefix1 ||| i1).val +
                      (off - subtreeCapacity packing_factor child_depth) := by
                  rw [hrp_val, ← hchild_capacity]
                  omega
                rw [heq] at hoff3
                have := hR_bounded
                  (off - subtreeCapacity packing_factor child_depth)
                  (by omega) hoff3
                omega
              have hdense_right := ih new_depth (prefix1 ||| i1) right
                new_right child_depth right_len nlR (hmeasure_child right)
                hnd_depth (UpdateReady.ofDense right_dense) halign_right
                hR_old_le hR_pos hR_cap hR_complete hR_bounded hr1
              rw [hnl_sum]
              exact DenseTree.node packing_factor hash new_left new_right
                child_depth nlL nlR hdense_left hdense_right hnlL_pos
                hside_full

/-- **Bulk-update preservation.** A successful `with_updated_leaves` from
    the root prefix on a dense tree is dense at the new length of the update
    domain. Besides the packing layout and the input density, the premises
    are: the update domain itself, its two feasibility bounds (a positive new
    length, since a Zero tree with no updates would otherwise produce a
    non-canonical empty packed leaf, and the subtree capacity bound), and
    lawfulness of the two `UpdateMap` methods on the answers they actually
    return: `get` reflects the update set, `has_any_in_range` decides its
    restriction to a range. -/
theorem with_updated_leaves_preserves_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) {updates : U}
    {packing_factor : Option Std.Usize} {packing_depth depth : Std.Usize}
    {tree : Tree T} {updated : triomphe.arc.Arc (Tree T)}
    {old_len new_len : Nat} {has_update : Nat → Prop}
    {hashes : Option (alloc.collections.btree.map.BTreeMap
      (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hlayout : PackingLayout ValueInst packing_factor packing_depth)
    (hdense : DenseTree packing_factor tree depth.val old_len)
    (hdomain : DenseUpdateDomain old_len new_len has_update)
    (hnew_pos : 0 < new_len)
    (hnew_cap : new_len ≤ subtreeCapacity packing_factor depth.val)
    (hget : ∀ (i : Std.Usize) (found : Option T),
      mapInst.get updates i = ok found →
      (found.isSome = true ↔ has_update i.val))
    (hrange : ∀ (lo hi : Std.Usize) (r : Bool),
      mapInst.has_any_in_range updates lo hi = ok r →
      (r = true ↔ ∃ j, lo.val ≤ j ∧ j < hi.val ∧ has_update j))
    (hupdate : Tree.with_updated_leaves ValueInst mapInst tree updates
      0#usize depth hashes = ok (core.result.Result.Ok updated)) :
    DenseTree packing_factor updated depth.val new_len := by
  obtain ⟨hmono, hcomplete, hbounded⟩ := hdomain
  refine with_updated_leaves_preserves_dense_aux ValueInst mapInst updates
    hlayout hget hrange hashes (2 * depth.val + updateZbit tree) depth
    0#usize tree updated depth.val old_len new_len (Nat.le_refl _) rfl
    (UpdateReady.ofDense hdense) (by simp) hmono hnew_pos hnew_cap ?_ ?_
    hupdate
  · intro j h1 h2
    simpa using hcomplete j h1 h2
  · intro j hj hup
    exact hbounded j (by simpa using hup)

end milhouse.tree
