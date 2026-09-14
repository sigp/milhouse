import Tree.Builder.Metadata

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

private theorem max_tree_depth_eq : MAX_TREE_DEPTH = ok 63#usize := by
  have hcast : UScalar.cast .Usize core.num.U64.BITS = 64#usize := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq, UScalarTy.Usize_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all [core.num.U64.BITS]
  obtain ⟨result, hsub, hrval, _⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := 64#usize) (y := 1#usize) (by decide))
  have heq : result = 63#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hrval
  subst result
  simp only [MAX_TREE_DEPTH, hcast, lift, bind_tc_ok, hsub]

/-- A representable subtree capacity makes builder initialization succeed.
Its checked addition, shift, and depth guard follow from that capacity bound;
the initial level does not affect constructor success. -/
theorem Builder.new_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) (depth level : Std.Usize)
    (hcapacity : subtreeCapacity factor depth.val ≤ Std.Usize.max) :
    ∃ self, Builder.new ValueInst depth level = ok (core.result.Result.Ok self) := by
  have hmax : Std.Usize.max < 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all [Std.Usize.max, Std.Usize.numBits]
  have hpower : 2 ^ (depth.val + packingDepth.val) ≤ Std.Usize.max := by
    simpa only [hlayout.subtreeCapacity_eq_two_pow, Nat.add_comm] using hcapacity
  have hbits : depth.val + packingDepth.val < System.Platform.numBits := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt h)
    omega
  have hsumBound : depth.val + packingDepth.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    cases System.Platform.numBits_eq <;> simp_all [Std.Usize.max, Std.Usize.numBits] <;> omega
  obtain ⟨sum, hadd, hsum⟩ := WP.spec_imp_exists (UScalar.add_spec hsumBound)
  have hsaturating : core.num.Usize.saturating_add depth packingDepth = sum := by
    apply UScalar.eq_of_val_eq
    simp only [core.num.Usize.saturating_add, UScalar.saturating_add, UScalar.val]
    have hb : depth.bv.toNat + packingDepth.bv.toNat ≤ UScalar.max .Usize := hsumBound
    rw [min_eq_right hb, BitVec.toNat_ofNat]
    change (depth.val + packingDepth.val) % 2 ^ UScalarTy.Usize.numBits = sum.val
    rw [← hsum, Nat.mod_eq_of_lt sum.hBounds]
  have hguard : ¬ sum > 63#usize := by
    change ¬ sum.val > 63
    cases System.Platform.numBits_eq <;> omega
  have hshift : sum.val < UScalarTy.Usize.numBits := by
    simpa only [hsum, UScalarTy.Usize_numBits_eq] using hbits
  obtain ⟨capacity, hshiftResult, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec (1#usize) sum (UScalar.size .Usize) hshift rfl)
  refine ⟨{ stack := alloc.vec.Vec.with_capacity (utils.MaybeArced (tree.Tree T)) depth
            depth := depth
            level := level
            length := 0#usize
            packing_factor := factor
            packing_depth := packingDepth
            capacity := capacity }, ?_⟩
  simp only [Builder.new, hlayout.opt_packing_depth_eq,
    hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok, hsaturating, max_tree_depth_eq,
    hguard, ↓reduceIte, hadd, hshiftResult, hlayout.opt_packing_factor_eq]

/-- Successful initialization and the complete empty builder invariant from
the caller's layout, level interpretation, and representable capacity. -/
theorem Builder.new_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) (depth level : Std.Usize)
    (hcapacity : subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hlevel : level.val = 0 ∨ packingDepth.val ≤ level.val)
    (hlevelBound : level.val ≤ depth.val + packingDepth.val) :
    ∃ self, Builder.new ValueInst depth level = ok (core.result.Result.Ok self) ∧
      BuilderInvariant ValueInst self ∧ self.elements = [] ∧
      self.depth = depth ∧ self.level = level ∧ self.length = 0#usize := by
  obtain ⟨self, hnew⟩ := Builder.new_success ValueInst hlayout depth level hcapacity
  exact ⟨self, hnew, builder_new_establishes_invariant ValueInst hlayout depth level
    hlevel hlevelBound hnew, Builder.new_elements ValueInst depth level hnew,
    Builder.new_parameters ValueInst depth level hnew⟩

end milhouse.builder
