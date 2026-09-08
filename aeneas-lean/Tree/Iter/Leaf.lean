import Tree.Iter.Construction
import Tree.Iter.Path.Contents
import Tree.Iter.Path.Backtrack

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.builder

namespace milhouse.iter

/-- Popping and immediately restoring the current shared node succeeds and
    leaves the stack unchanged, even at the maximum vector length. -/
theorem vec_pop_push_same {T : Type} (stack : alloc.vec.Vec T)
    (completed : _root_.List T) (node : T) (hstack : stack.val = completed ++ [node]) :
    ∃ rest, alloc.vec.Vec.pop Global stack = ok (some node, rest) ∧
      alloc.vec.Vec.push rest node = ok stack := by
  obtain ⟨entry, rest, hpop, _⟩ := vec_pop_spec stack
  cases entry with
  | none =>
    have hempty := (vec_pop_none_values hpop).1
    simp [hstack] at hempty
  | some actual =>
    have hsource := vec_pop_some_values hpop
    have hlast := congrArg _root_.List.getLast? hsource
    have heq : actual = node := by simpa [hstack] using hlast.symm
    subst actual
    have hroom : rest.val.length < Usize.max := by
      have hbound := stack.property
      rw [hsource] at hbound
      simp only [_root_.List.length_append, _root_.List.length_singleton] at hbound
      omega
    obtain ⟨rebuilt, hpush, hvalues⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec rest node hroom)
    have heq : rebuilt = stack := Subtype.ext (hvalues.trans hsource.symm)
    subst rebuilt
    exact ⟨rest, hpop, hpush⟩

/-- The machine operations computing an unpacked leaf's backtracking count
    succeed, and the resulting count is the exact trailing-zero valuation plus
    one. Positivity follows from the successful cursor increment. -/
theorem leaf_pop_count {next : Std.Usize} (hpositive : 0 < next.val) :
    ∃ zeros count, core.num.Usize.trailing_zeros next = ok zeros ∧
      UScalar.cast .Usize zeros + 1#usize = ok count ∧
      count.val = padicValNat 2 next.val + 1 := by
  let zeros : Std.U32 := ⟨BitVec.ofNat 32 (TreeAux.bvTrailingZeros next.bv)⟩
  have hzeros : core.num.Usize.trailing_zeros next = ok zeros := rfl
  have hvaluation := usize_trailing_zeros_padic hpositive hzeros
  have hbound : zeros.val < System.Platform.numBits := by
    have hpow : 2 ^ padicValNat 2 next.val ≤ next.val :=
      Nat.le_of_dvd hpositive pow_padicValNat_dvd
    have hnext : next.val < 2 ^ System.Platform.numBits := by simpa using next.hBounds
    by_contra hnot
    have hle := Nat.pow_le_pow_right (n := 2) (by omega)
      (show System.Platform.numBits ≤ padicValNat 2 next.val by omega)
    omega
  have hcast : (UScalar.cast .Usize zeros).val = zeros.val := by
    apply UScalar.cast_val_mod_pow_greater_numBits_eq
    simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
    cases System.Platform.numBits_eq <;> omega
  obtain ⟨count, hcount, hvalue⟩ := usize_add_succeeds
    (x := UScalar.cast .Usize zeros) (y := 1#usize)
    (by
      have hpow : System.Platform.numBits < 2 ^ System.Platform.numBits := Nat.lt_two_pow_self
      simpa [hcast] using (show zeros.val + 1 < 2 ^ System.Platform.numBits by omega))
  have hc : count.val = zeros.val + 1 := by simpa [hcast] using hvalue
  exact ⟨zeros, count, hzeros, hcount, by omega⟩

/-- The extracted leaf branch returns the stored value, advances the index
    once, and removes precisely the trailing-zero suffix of the saved path. -/
theorem Iter.next_leaf_step {T : Type} (ValueInst : Value T) (self : Iter T)
    (completed : _root_.List (tree.Tree T)) (value : leaf.Leaf T)
    (hstack : self.stack.val = completed ++ [.Leaf value])
    (hlive : self.index < self.length) :
    ∃ next rest, Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        ok (some value.value, { self with index := next, stack := rest }) ∧
      next.val = self.index.val + 1 ∧
      rest.val = self.stack.val.take (self.stack.val.length - (padicValNat 2 next.val + 1)) := by
  obtain ⟨rest, hpop, hpush⟩ := vec_pop_push_same self.stack completed (.Leaf value) hstack
  have hbound : self.index.val + 1 < 2 ^ System.Platform.numBits := by
    have hlen : self.length.val < 2 ^ System.Platform.numBits := by simpa using self.length.hBounds
    have hlt : self.index.val < self.length.val := by simpa only [UScalar.lt_equiv] using hlive
    omega
  obtain ⟨next, hnext, hnextVal⟩ := usize_add_succeeds (x := self.index) (y := 1#usize) (by simpa using hbound)
  have hvalue : next.val = self.index.val + 1 := by simpa using hnextVal
  obtain ⟨zeros, count, hzeros, hcount, hcountVal⟩ := leaf_pop_count (next := next) (by omega)
  obtain ⟨finalStack, hback, hfinal⟩ := pop_many_spec self.stack count
  refine ⟨next, finalStack, ?_, hvalue, ?_⟩
  · rw [Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
    simp! only [utils.Length.as_usize, bind_tc_ok, if_neg (not_le_of_gt hlive), hpop,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch, hpush,
      triomphe.arc.Arc.Insts.CoreConvertAsRef.as_ref, hnext, hzeros, lift, hcount, hback]
  · simpa [hcountVal] using hfinal

/-- For a valid live cursor whose current frame is an unpacked leaf, the
    extracted `next` returns the root sequence's indexed value and preserves
    the complete cursor invariant. No arithmetic-success premise is needed. -/
theorem Iter.next_leaf_spec {T : Type} (ValueInst : Value T)
    {root : tree.Tree T} {depth : Std.Usize} {length : utils.Length} {self : Iter T}
    (hdense : DenseTree none root depth.val length.val)
    (hvalid : Iter.Valid root depth none 0#usize length self)
    (completed : _root_.List (tree.Tree T)) (value : leaf.Leaf T)
    (hstack : self.stack.val = completed ++ [.Leaf value])
    (hlive : self.index < length) :
    ∃ next, Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        ok (root.elements[self.index.val]?, next) ∧
      next.index.val = self.index.val + 1 ∧
      Iter.Valid root depth none 0#usize length next := by
  obtain ⟨hdepth, hfactor, hpacking, hlength, hpath, _⟩ := hvalid
  have hpathTop : Path 0 root depth.val self.index.val (completed ++ [.Leaf value]) := by
    simpa [hstack] using hpath
  obtain ⟨hshape, hslot⟩ := hpathTop.top completed (by simp [leafCapacity]) hdense.shape
  have hzero : depth.val - completed.length = 0 := by
    generalize hremaining : depth.val - completed.length = remaining at hshape
    cases hshape
    rfl
  have hfull : self.stack.val.length = depth.val + 1 := by
    have hlen := hpath.length_le
    have hstackLen : self.stack.val.length = completed.length + 1 := by simp [hstack]
    omega
  have hliveVal : self.index.val < length.val := by simpa only [UScalar.lt_equiv] using hlive
  have hinside : self.index.val < subtreeCapacity none depth.val :=
    hliveVal.trans_le hdense.length_le_capacity
  have hrootSlot := hdense.slot_eq_elements_mod self.index.val
  rw [Nat.mod_eq_of_lt hinside] at hrootSlot
  have hlookup : root.elements[self.index.val]? = some value.value := by
    rw [← hrootSlot, hslot]
    rfl
  obtain ⟨index, rest, hstep, hindex, hrest⟩ := Iter.next_leaf_step ValueInst self completed value
    hstack (by simpa [hlength] using hlive)
  refine ⟨{ self with index, stack := rest }, ?_, hindex, ?_⟩
  · simpa [hlookup] using hstep
  · refine ⟨hdepth, hfactor, hpacking, hlength, ?_, ?_⟩
    · change Path 0 root depth.val index.val rest.val
      rw [hrest, hindex]
      simpa using hpath.backtrack hfull (by simp)
    · intro hnextlive
      change rest.val ≠ []
      rw [hrest, hindex]
      apply backtrack_nonempty (packingDepth := 0) hfull (by simp)
      have hbound := hdense.length_le_capacity
      simp only [subtreeCapacity, leafCapacity, Nat.one_mul] at hbound
      change index.val < length.val at hnextlive
      simp only [Nat.add_zero]
      omega

end milhouse.iter
