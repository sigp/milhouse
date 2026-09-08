import Tree.Iter.Leaf

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

/-- At a packed-chunk boundary, the checked subtraction in the actual
    backtracking calculation cannot underflow. Both casts and the final
    addition succeed and yield the packing-adjusted trailing-zero count. -/
theorem packed_pop_count {next packingDepth : Std.Usize}
    (hpositive : 0 < next.val) (hboundary : 2 ^ packingDepth.val ∣ next.val) :
    ∃ zeros toPop count,
      core.num.Usize.trailing_zeros next = ok zeros ∧
      U32.checked_sub zeros (UScalar.cast .U32 packingDepth) = some toPop ∧
      UScalar.cast .Usize toPop + 1#usize = ok count ∧
      count.val = padicValNat 2 next.val - packingDepth.val + 1 := by
  obtain ⟨zeros, leafCount, hzeros, _, hleafCount⟩ := leaf_pop_count hpositive
  have hvaluation := usize_trailing_zeros_padic hpositive hzeros
  have hpacking : packingDepth.val ≤ zeros.val := by
    rw [hvaluation]
    exact (padicValNat_dvd_iff_le (p := 2) (by omega)).mp hboundary
  have hpackingBound : packingDepth.val < 2 ^ 32 := by
    have hzerosBound : zeros.val < 2 ^ 32 := by simpa using zeros.hBounds
    omega
  have hcast : (UScalar.cast .U32 packingDepth).val = packingDepth.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    simpa only [UScalarTy.U32_numBits_eq] using hpackingBound
  obtain ⟨toPop, hsub, hsubVal, _⟩ := WP.spec_imp_exists
    (U32.sub_spec (x := zeros) (y := UScalar.cast .U32 packingDepth) (by scalar_tac))
  have hchecked : U32.checked_sub zeros (UScalar.cast .U32 packingDepth) = some toPop := by
    simp [U32.checked_sub, core.num.checked_sub_UScalar, hsub, Option.ofResult]
  have hcastPop : (UScalar.cast .Usize toPop).val = toPop.val := by
    apply UScalar.cast_val_mod_pow_greater_numBits_eq
    simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
    cases System.Platform.numBits_eq <;> omega
  have hvalue : toPop.val = padicValNat 2 next.val - packingDepth.val := by
    simpa [hcast, hvaluation] using hsubVal
  have hroom : toPop.val + 1 < 2 ^ System.Platform.numBits := by
    have hbound : leafCount.val < 2 ^ System.Platform.numBits := by simpa using leafCount.hBounds
    omega
  obtain ⟨count, hcount, hcountVal⟩ := usize_add_succeeds
    (x := UScalar.cast .Usize toPop) (y := 1#usize) (by simpa [hcastPop] using hroom)
  exact ⟨zeros, toPop, count, hzeros, hchecked, hcount, by simpa [hcastPop, hvalue] using hcountVal⟩

/-- The final slot of a chunk is exactly the index whose successor is aligned
    to the next chunk. This relates the Rust remainder test to divisibility. -/
theorem chunk_boundary_iff {index capacity : Nat} (hcapacity : 0 < capacity) :
    index % capacity + 1 = capacity ↔ capacity ∣ index + 1 := by
  have hmod := Nat.mod_lt index hcapacity
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  constructor
  · intro hlast
    have hsum : (index % capacity + 1) % capacity = 0 := by rw [hlast]; simp
    simpa [Nat.add_mod] using hsum
  · intro hnext
    have hsum : (index % capacity + 1) % capacity = 0 := by simpa [Nat.add_mod] using hnext
    have hdvd := Nat.dvd_of_mod_eq_zero hsum
    have hle := Nat.le_of_dvd (by omega : 0 < index % capacity + 1) hdvd
    omega

/-- The actual packed-leaf branch returns the selected slot and advances once.
    It keeps the stack inside a chunk and truncates the exact backtracking
    suffix at a boundary, deriving every checked-operation bound internally. -/
theorem Iter.next_packed_step {T : Type} (ValueInst : Value T) (self : Iter T)
    (completed : _root_.List (tree.Tree T)) (value : packed_leaf.PackedLeaf T)
    (hstack : self.stack.val = completed ++ [.PackedLeaf value])
    (hlive : self.index < self.length)
    (hpower : self.packing_factor.val = 2 ^ self.packing_depth.val) :
    ∃ next rest, Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        ok (value.values.val[self.index.val % self.packing_factor.val]?,
          { self with index := next, stack := rest }) ∧
      next.val = self.index.val + 1 ∧
      rest.val = if self.packing_factor.val ∣ next.val then
        self.stack.val.take (self.stack.val.length -
          (padicValNat 2 next.val - self.packing_depth.val + 1)) else self.stack.val := by
  obtain ⟨rest, hpop, hpush⟩ := vec_pop_push_same self.stack completed (.PackedLeaf value) hstack
  have hfactor : 0 < self.packing_factor.val := by rw [hpower]; positivity
  obtain ⟨subIndex, hrem, hremVal⟩ := usize_rem_succeeds self.index hfactor
  have hread : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T)
      (alloc.vec.Vec.deref value.values) subIndex = ok value.values.val[subIndex.val]? := rfl
  have hbound : self.index.val + 1 < 2 ^ System.Platform.numBits := by
    have hlen : self.length.val < 2 ^ System.Platform.numBits := by simpa using self.length.hBounds
    have hlt : self.index.val < self.length.val := by simpa only [UScalar.lt_equiv] using hlive
    omega
  obtain ⟨next, hnext, hnextVal⟩ := usize_add_succeeds (x := self.index) (y := 1#usize) (by simpa using hbound)
  have hnextValue : next.val = self.index.val + 1 := by simpa using hnextVal
  have hsubBound : subIndex.val + 1 < 2 ^ System.Platform.numBits := by
    have hmod := Nat.mod_lt self.index.val hfactor
    have hmax : self.packing_factor.val < 2 ^ System.Platform.numBits := by simpa using self.packing_factor.hBounds
    omega
  obtain ⟨subNext, hsubNext, hsubNextVal⟩ := usize_add_succeeds (x := subIndex) (y := 1#usize)
    (by simpa using hsubBound)
  have hsubValue : subNext.val = self.index.val % self.packing_factor.val + 1 := by
    simpa [hremVal] using hsubNextVal
  have hboundary : subNext = self.packing_factor ↔ self.packing_factor.val ∣ next.val := by
    constructor
    · intro heq
      have hv := congrArg UScalar.val heq
      rw [hsubValue] at hv
      rw [hnextValue]
      exact (chunk_boundary_iff hfactor).mp hv
    · intro hdiv
      apply UScalar.eq_of_val_eq
      rw [hsubValue]
      exact (chunk_boundary_iff hfactor).mpr (by simpa [hnextValue] using hdiv)
  by_cases hlast : subNext = self.packing_factor
  · have hdiv := hboundary.mp hlast
    obtain ⟨zeros, toPop, count, hzeros, hchecked, hcount, hcountVal⟩ :=
      packed_pop_count (next := next) (packingDepth := self.packing_depth) (by omega)
        (by rwa [← hpower])
    obtain ⟨finalStack, hback, hfinal⟩ := pop_many_spec self.stack count
    refine ⟨next, finalStack, ?_, hnextValue, ?_⟩
    · rw [Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
      simp! only [utils.Length.as_usize, bind_tc_ok, if_neg (not_le_of_gt hlive), hpop,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch, hpush, hrem, hread,
        hnext, hsubNext, if_pos hlast, hzeros, lift, hchecked, core.option.Option.expect,
        hcount, hback, hremVal]
    · simpa only [if_pos hdiv, hcountVal] using hfinal
  · have hdiv : ¬ self.packing_factor.val ∣ next.val := fun h => hlast (hboundary.mpr h)
    refine ⟨next, self.stack, ?_, hnextValue, by rw [if_neg hdiv]⟩
    rw [Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
    simp! only [utils.Length.as_usize, bind_tc_ok, if_neg (not_le_of_gt hlive), hpop,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch, hpush, hrem, hread,
      hnext, hsubNext, if_neg hlast, hremVal]

/-- A live packed-leaf step returns the root sequence's indexed value,
    advances once, and preserves the complete cursor invariant. Geometry,
    stack bounds, and chunk-boundary safety follow from the input invariant. -/
theorem Iter.next_packed_spec {T : Type} (ValueInst : Value T)
    {root : tree.Tree T} {depth factor packingDepth : Std.Usize}
    {length : utils.Length} {self : Iter T}
    (hpower : factor.val = 2 ^ packingDepth.val)
    (hdense : DenseTree (some factor) root depth.val length.val)
    (hvalid : Iter.Valid root depth (some factor) packingDepth length self)
    (completed : _root_.List (tree.Tree T)) (value : packed_leaf.PackedLeaf T)
    (hstack : self.stack.val = completed ++ [.PackedLeaf value])
    (hlive : self.index < length) :
    ∃ next, Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        ok (root.elements[self.index.val]?, next) ∧
      next.index.val = self.index.val + 1 ∧
      Iter.Valid root depth (some factor) packingDepth length next := by
  obtain ⟨hdepth, hfactor, hpacking, hlength, hpath, _⟩ := hvalid
  have hf : self.packing_factor = factor := by simpa using hfactor
  have hpathTop : Path packingDepth.val root depth.val self.index.val
      (completed ++ [.PackedLeaf value]) := by simpa [hstack] using hpath
  obtain ⟨hshape, hslot⟩ := hpathTop.top completed (by simpa [leafCapacity] using hpower) hdense.shape
  have hzero : depth.val - completed.length = 0 := by
    generalize hremaining : depth.val - completed.length = remaining at hshape
    cases hshape
    rfl
  have hfull : self.stack.val.length = depth.val + 1 := by
    have hlen := hpath.length_le
    have hstackLen : self.stack.val.length = completed.length + 1 := by simp [hstack]
    omega
  have hliveVal : self.index.val < length.val := by simpa only [UScalar.lt_equiv] using hlive
  have hinside : self.index.val < subtreeCapacity (some factor) depth.val :=
    hliveVal.trans_le hdense.length_le_capacity
  have hrootSlot := hdense.slot_eq_elements_mod self.index.val
  rw [Nat.mod_eq_of_lt hinside] at hrootSlot
  have hlookup : root.elements[self.index.val]? = value.values.val[self.index.val % factor.val]? := by
    rw [← hrootSlot, hslot]
    rfl
  obtain ⟨index, rest, hstep, hindex, hrest⟩ := Iter.next_packed_step ValueInst self completed value
    hstack (by simpa [hlength] using hlive) (by simpa [hf, hpacking] using hpower)
  rw [hf, hpacking] at hrest
  refine ⟨{ self with index, stack := rest }, ?_, hindex, ?_⟩
  · simpa [hlookup, hf] using hstep
  · refine ⟨hdepth, hfactor, hpacking, hlength, ?_, ?_⟩
    · change Path packingDepth.val root depth.val index.val rest.val
      rw [hrest, hindex]
      split_ifs with hboundary
      · exact hpath.backtrack hfull (by rwa [← hpower])
      · exact hpath.advance_in_chunk hfull (by rwa [← hpower])
    · intro hnextlive
      change rest.val ≠ []
      rw [hrest, hindex]
      split_ifs with hboundary
      · apply backtrack_nonempty hfull (by rwa [← hpower])
        have hcap : subtreeCapacity (some factor) depth.val = 2 ^ (depth.val + packingDepth.val) := by
          simp [subtreeCapacity, leafCapacity, hpower, pow_add, Nat.mul_comm]
        have hbound := hdense.length_le_capacity
        rw [hcap] at hbound
        change index.val < length.val at hnextlive
        omega
      · intro hempty
        have hlen := congrArg _root_.List.length hempty
        rw [hfull] at hlen
        simp at hlen

end milhouse.iter
