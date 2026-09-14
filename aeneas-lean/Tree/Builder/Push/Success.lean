import Tree.Builder.Push.Loop
import Tree.PackedLeaf.Push
import Tree.Builder.Contents.Push

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- A valid leaf-level builder with spare capacity accepts every supplied
value. Its stack shape, carry count, leaf capacity and machine bounds are
derived internally; no clone law or assumed successful subcall is needed. -/
theorem Builder.push_success {T : Type} {ValueInst : Value T}
    (self : Builder T) (hinvariant : BuilderInvariant ValueInst self)
    (hlevel : self.level.val = 0) (hspare : self.length.val < self.capacity.val) (value : T) :
    ∃ result, Builder.push ValueInst self value = ok (core.result.Result.Ok (), result) := by
  have hlayout := BuilderInvariant.layout hinvariant
  have hstack : BuilderStack self.packing_factor 0 self.stack.val self.depth.val self.length.val := by
    simpa only [hlevel, ↓reduceIte] using BuilderInvariant.stack_dense hinvariant
  have hcapacity := BuilderInvariant.builder_capacity_matches hinvariant
  have hfits : self.length.val + 1 ≤ subtreeCapacity self.packing_factor self.depth.val := by omega
  have hbound : self.length.val + (1#usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hc : self.capacity.val ≤ Std.Usize.max := by scalar_tac
    change self.length.val + 1 ≤ Std.Usize.max
    omega
  obtain ⟨nextIndex, hadd, hnext⟩ := WP.spec_imp_exists (UScalar.add_spec hbound)
  obtain ⟨zeros, hzeros⟩ : ∃ zeros, core.num.Usize.trailing_zeros nextIndex = ok zeros := ⟨_, rfl⟩
  have hnotFull : self.length ≠ self.capacity := by
    intro heq
    have := congrArg UScalar.val heq
    omega
  let range : core.ops.range.Range Std.U32 :=
    { start := 0#u32, «end» := core.num.U32.saturating_sub zeros (UScalar.cast .U32 self.packing_depth) }
  cases hfactor : self.packing_factor with
  | none =>
    rw [hfactor] at hlayout hstack hfits
    obtain ⟨top, hleaf, hdense⟩ := leaf_unboxed_preserves_dense ValueInst value
    obtain ⟨forest, length, hloop⟩ := Builder.push_loop0_append_success hlayout self.stack
      self.length nextIndex zeros top hstack hdense (by decide)
      (by exact Nat.mod_one _) hfits rfl hnext hzeros
    refine ⟨{ self with stack := forest, length }, ?_⟩
    simp! only [Builder.push, utils.Length.as_usize, bind_tc_ok, hnotFull, ↓reduceIte,
      hadd, hfactor, hleaf, hzeros, lift, hloop]
  | some factor =>
    rw [hfactor] at hlayout hstack hfits
    by_cases haligned : self.length.val % factor.val = 0
    · have hmultiple : core.num.Usize.is_multiple_of self.length factor = ok true := by
        simp [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, haligned]
      obtain ⟨leaf, hsingle, hdense⟩ := packedLeaf_single_preserves_dense ValueInst hlayout value
      obtain ⟨forest, length, hloop⟩ := Builder.push_loop0_append_success hlayout self.stack
        self.length nextIndex zeros (.PackedLeaf leaf) hstack hdense (by decide)
        (by simpa only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] using haligned)
        hfits rfl hnext hzeros
      have hloop1 : Builder.push_loop1 ValueInst range self.stack self.length (.PackedLeaf leaf) =
          ok (core.result.Result.Ok (), forest, length) := hloop
      dsimp only [range] at hloop1
      refine ⟨{ self with stack := forest, length }, ?_⟩
      simp! only [Builder.push, utils.Length.as_usize, bind_tc_ok, hnotFull, ↓reduceIte,
        hadd, hfactor, hmultiple, hsingle, hzeros, lift, hloop1]
    · have hmultiple : core.num.Usize.is_multiple_of self.length factor = ok false := by
        simp [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, haligned]
      have hpartial : self.length.val % subtreeCapacity self.packing_factor 0 ≠ 0 := by
        simpa only [hfactor, subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] using haligned
      obtain ⟨baseStack, top, topLen, hentries, hdense, hpositive, htopPartial⟩ :=
        BuilderInvariant.partial_leaf hinvariant hlevel hpartial
      rw [hfactor] at hdense htopPartial
      obtain ⟨baseLen, hlength, hbaseAligned, hbase⟩ := hstack.remove_partial_last hlayout
        hentries hdense hpositive htopPartial
      generalize hdepth : (0 : Nat) = depth at hdense
      cases hdense with
      | zero => omega
      | node => omega
      | packed factor leaf hnonempty hleafFits =>
        have hleafSpare : leaf.values.val.length < factor.val := by
          simpa only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] using htopPartial
        obtain ⟨leaf1, hpush, _⟩ := packed_leaf.PackedLeaf.push_success
          ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst leaf value factor
          hlayout.tree_hash_packing_factor_eq hleafSpare
        have hdense1 := packedLeaf_push_preserves_dense ValueInst hlayout
          (DenseTree.packed factor leaf hnonempty hleafFits) value hpush
        obtain ⟨rest, hpop, hrest⟩ := vec_pop_append_last (A := Global) self.stack baseStack
          (.Unarced (.PackedLeaf leaf)) hentries
        obtain ⟨forest, length, hloop⟩ := Builder.push_loop0_append_success hlayout rest
          self.length nextIndex zeros (.PackedLeaf leaf1) (by simpa only [hrest] using hbase)
          hdense1 (by omega) hbaseAligned (by omega) (by omega) hnext hzeros
        have hloop2 : Builder.push_loop2 ValueInst range rest self.length (.PackedLeaf leaf1) =
            ok (core.result.Result.Ok (), forest, length) := hloop
        dsimp only [range] at hloop2
        refine ⟨{ self with stack := forest, length }, ?_⟩
        simp! only [Builder.push, utils.Length.as_usize, bind_tc_ok, hnotFull, ↓reduceIte,
          hadd, hfactor, hmultiple, Bool.false_eq_true, ↓reduceIte, hpop, hpush,
          core.result.Result.Insts.CoreOpsTry.branch, hzeros, lift, hloop2]

/-- Total value insertion appends the exact supplied value, increments length,
and preserves the complete invariant of a builder with spare capacity. -/
theorem Builder.push_spec {T : Type} {ValueInst : Value T}
    (self : Builder T) (hinvariant : BuilderInvariant ValueInst self)
    (hlevel : self.level.val = 0) (hspare : self.length.val < self.capacity.val) (value : T) :
    ∃ result, Builder.push ValueInst self value = ok (core.result.Result.Ok (), result) ∧
      BuilderInvariant ValueInst result ∧ result.elements = self.elements ++ [value] ∧
      result.length.val = self.length.val + 1 := by
  obtain ⟨result, hpush⟩ := Builder.push_success self hinvariant hlevel hspare value
  exact ⟨result, hpush, builder_push_preserves_invariant hinvariant hlevel value hpush,
    Builder.push_elements ValueInst self value hpush⟩

end milhouse.builder
