import Tree.Invariants
import Tree.Lemmas

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Tree geometry without a density requirement. In particular, a node with
    two empty children is permitted: bulk updates create this intermediate
    shape when expanding a zero subtree. -/
inductive Tree.Shape {T : Type} : Option Std.Usize → Tree T → Nat → Prop where
  | zero (factor : Option Std.Usize) (depth : Std.Usize) :
      Tree.Shape factor (.Zero depth) depth.val
  | leaf (value : leaf.Leaf T) : Tree.Shape none (.Leaf value) 0
  | packed (factor : Std.Usize) (value : packed_leaf.PackedLeaf T) :
      Tree.Shape (some factor) (.PackedLeaf value) 0
  | node {factor : Option Std.Usize} {left right : Tree T} {depth : Nat}
      (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hleft : Tree.Shape factor left depth) (hright : Tree.Shape factor right depth) :
      Tree.Shape factor (.Node hash left right) (depth + 1)

theorem DenseTree.shape {T : Type} {factor : Option Std.Usize}
    {self : Tree T} {depth length : Nat} (h : DenseTree factor self depth length) :
    self.Shape factor depth := by
  induction h with
  | zero factor depth => exact .zero factor depth
  | leaf value => exact .leaf value
  | packed factor value _ _ => exact .packed factor value
  | node _ hash _ _ _ _ _ _ _ _ _ ihleft ihright => exact .node hash ihleft ihright

/-- Pure slot contents at the given binary depth. Like extracted lookup,
    routing wraps modulo the subtree capacity. This model records values and
    holes; it does not assert that a tree is dense. -/
def Tree.slot {T : Type} (factor : Option Std.Usize) (self : Tree T)
    (depth index : Nat) : Option T :=
  match self with
  | .Zero _ => none
  | .Leaf value => some value.value
  | .PackedLeaf value => value.values.val[index % leafCapacity factor]?
  | .Node _ left right =>
    match depth with
    | 0 => none
    | child + 1 =>
      if index % subtreeCapacity factor (child + 1) < subtreeCapacity factor child
      then left.slot factor child index else right.slot factor child index

/-- Extracted lookup agrees with slot contents on every geometrically valid
    tree, including sparse and transient empty-node shapes. Only the routing
    shift bound is needed beyond shape and packing layout. -/
theorem Tree.Shape.get_recursive_eq_slot {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    {self : Tree T} {depth : Nat} (hshape : self.Shape factor depth)
    (hlayout : PackingLayout ValueInst factor packingDepth) :
    ∀ (machineDepth : Std.Usize), machineDepth.val = depth →
      depth + packingDepth.val ≤ System.Platform.numBits →
      ∀ index, Tree.get_recursive ValueInst self index machineDepth packingDepth =
        ok (self.slot factor depth index.val) := by
  induction hshape with
  | zero factor depth =>
    intro machineDepth hdepth hbits index
    exact get_recursive_zero ValueInst depth index machineDepth packingDepth
  | leaf value =>
    intro machineDepth hdepth hbits index
    have hz : machineDepth = 0#usize := by scalar_tac
    subst machineDepth
    exact get_recursive_leaf ValueInst value index packingDepth
  | packed factor value =>
    intro machineDepth hdepth hbits index
    have hz : machineDepth = 0#usize := by scalar_tac
    subst machineDepth
    have hfactor := hlayout.tree_hash_packing_factor_eq
    have hpos : 0 < factor.val := by simpa [leafCapacity] using hlayout.leafCapacity_pos
    obtain ⟨sub, hrem, hsub⟩ := usize_rem_succeeds index hpos
    simp [Tree.get_recursive, Tree.slot, leafCapacity, hfactor, hrem, hsub,
      core.slice.Slice.get, alloc.vec.Vec.deref]
  | @node factor left right child hash hleft hright ihleft ihright =>
    intro machineDepth hdepth hbits index
    have hpositive : machineDepth > 0#usize := by scalar_tac
    obtain ⟨nd, hnd, hndVal⟩ := usize_sub_one_succeeds
      (show 0 < machineDepth.val by scalar_tac)
    have hndDepth : nd.val = child := by omega
    have hnumbits : System.Platform.numBits < 2 ^ System.Platform.numBits := Nat.lt_two_pow_self
    obtain ⟨shift, hshift, hshiftVal⟩ :=
      usize_add_succeeds (x := nd) (y := packingDepth) (by omega)
    obtain ⟨shifted, hshr, _⟩ := usize_shift_right_succeeds index
      (show shift.val < System.Platform.numBits by omega)
    have hchildCap : subtreeCapacity factor child = 2 ^ shift.val := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    have hparentCap : subtreeCapacity factor (child + 1) = 2 ^ (shift.val + 1) := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    have hroute := routing_bit_zero_iff hshr
    rw [← hchildCap, ← hparentCap] at hroute
    unfold Tree.get_recursive
    simp only [if_pos hpositive, hnd, hshift, hshr, lift, bind_tc_ok,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
    rw [Tree.slot]
    by_cases hbit : (shifted &&& 1#usize) = 0#usize
    · rw [if_pos hbit, if_pos (hroute.mp hbit)]
      exact ihleft hlayout nd hndDepth (by omega) index
    · rw [if_neg hbit, if_neg (fun h => hbit (hroute.mpr h))]
      exact ihright hlayout nd hndDepth (by omega) index

end milhouse.tree
