import Tree.ProgressiveTree.Iter.Layer
import Tree.Iter.Contents

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

private theorem usize_le_max_of_lt_pow {n : Nat} (h : n < 2 ^ System.Platform.numBits) :
    n ≤ Std.Usize.max := by scalar_tac

private theorem usize_saturating_sub_val (length start : Std.Usize) :
    (core.num.Usize.saturating_sub length start).val = length.val - start.val := by
  change (length.val - start.val) % 2 ^ UScalarTy.Usize.numBits = length.val - start.val
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- Opening a dense progressive layer succeeds and installs a binary iterator
    that enumerates exactly the requested suffix of that layer. The spine's
    remaining length determines the binary iterator length; representable layer
    capacity supplies all depth arithmetic and binary routing bounds. -/
theorem ProgressiveTreeIter.enter_subtree_drains {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (left : tree.Tree T) (right : ProgressiveTree T)
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize))
    (hdense : (ProgressiveTree.ProgressiveNode hash left right).Dense factor self.prog_depth.val
      (self.length.val - progressiveCapacity factor self.prog_depth.val))
    (hfit : subtreeCapacity factor (2 * self.prog_depth.val) < 2 ^ System.Platform.numBits)
    (localIndex : Std.Usize) :
    ∃ next current, ProgressiveTreeIter.enter_subtree ValueInst self left right localIndex =
        ok { self with current_prog_node := some right, current_iter := some current, prog_depth := next } ∧
      next.val = self.prog_depth.val + 1 ∧
      IteratorDrains (iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
        current (left.elements.drop localIndex.val) := by
  obtain ⟨next, binary, hnext, hbinary, hbinaryVal, hbits⟩ := next_layer_bounds ValueInst hlayout self.prog_depth hfit
  have hnextVal : next.val = self.prog_depth.val + 1 := by
    have hadd := UScalar.add_equiv self.prog_depth 1#u32
    rw [hnext] at hadd
    simp at hadd
    omega
  obtain ⟨previous, hprevious, hpreviousVal, _⟩ := WP.spec_imp_exists
    (U32.sub_spec (x := next) (y := 1#u32) (by scalar_tac))
  have hpreviousEq : previous = self.prog_depth := by scalar_tac
  subst previous
  obtain ⟨start, _, hstart, _, hstartVal, _, _⟩ :=
    ProgressiveTree.layer_window ValueInst hlayout hnext hbinary (by simpa [hbinaryVal] using hfit)
  obtain ⟨capacity, hcapacity, hcapacityVal⟩ :=
    ProgressiveTree.capacity_successor_eq ValueInst hlayout.opt_packing_factor_eq hnext
  rw [min_eq_right (usize_le_max_of_lt_pow hfit)] at hcapacityVal
  let remaining := core.num.Usize.saturating_sub self.length start
  have hremaining : remaining.val = self.length.val - start.val :=
    usize_saturating_sub_val self.length start
  obtain ⟨subtreeLength, hmin, hminEq⟩ := WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_Usize.spec remaining capacity)
  have hsubtreeLength : subtreeLength.val =
      min (self.length.val - progressiveCapacity factor self.prog_depth.val)
        (subtreeCapacity factor (2 * self.prog_depth.val)) := by
    rw [hminEq, core.cmp.impls.OrdUsize.min_val, hremaining, hstartVal, hcapacityVal]
  have hleft : DenseTree factor left binary.val subtreeLength.val := by
    rw [hbinaryVal, hsubtreeLength]
    exact hdense.split_layer.1
  obtain ⟨current, hcurrent, hyields⟩ := iter.Iter.from_index_drains ValueInst hlayout hleft (by omega) localIndex
  refine ⟨next, current, ?_, hnextVal, hyields⟩
  dsimp only [remaining] at hmin
  unfold ProgressiveTreeIter.enter_subtree
  simp! only [hnext, hprevious, hstart, hbinary, hcapacity, lift, bind_tc_ok, hmin,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hcurrent]

/-- Layer entry enumerates the exact local suffix through its first `none`. -/
theorem ProgressiveTreeIter.enter_subtree_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTreeIter T) (left : tree.Tree T) (right : ProgressiveTree T)
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize))
    (hdense : (ProgressiveTree.ProgressiveNode hash left right).Dense factor self.prog_depth.val
      (self.length.val - progressiveCapacity factor self.prog_depth.val))
    (hfit : subtreeCapacity factor (2 * self.prog_depth.val) < 2 ^ System.Platform.numBits)
    (localIndex : Std.Usize) :
    ∃ next current, ProgressiveTreeIter.enter_subtree ValueInst self left right localIndex =
        ok { self with current_prog_node := some right, current_iter := some current, prog_depth := next } ∧
      next.val = self.prog_depth.val + 1 ∧
      IteratorYields (iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
        current (left.elements.drop localIndex.val) := by
  obtain ⟨next, current, henter, hdepth, hdrains⟩ :=
    ProgressiveTreeIter.enter_subtree_drains ValueInst hlayout self left right hash hdense hfit localIndex
  exact ⟨next, current, henter, hdepth, hdrains.yields⟩

end milhouse.progressive_tree
