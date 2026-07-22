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
    simpa [hresult] using heq

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
    | ok actual => rw [hfactor] at h; simp at h; simpa [h] using hfactor

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
