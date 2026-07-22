-- Structural invariants for milhouse trees.
import Tree.Funs
open Aeneas Aeneas.Std Result
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

end milhouse.tree
