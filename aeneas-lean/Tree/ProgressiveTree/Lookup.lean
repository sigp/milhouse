import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

private theorem next_layer_bounds {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) (depth : Std.U32)
    (hfit : subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits) :
    ∃ next binary, depth + 1#u32 = ok next ∧
      ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary ∧
      binary.val = 2 * depth.val ∧ binary.val + packingDepth.val < System.Platform.numBits := by
  have hbits : packingDepth.val + 2 * depth.val < System.Platform.numBits := by
    rw [hlayout.subtreeCapacity_eq_two_pow] at hfit
    by_contra hnot
    have hle : System.Platform.numBits ≤ packingDepth.val + 2 * depth.val := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega
  have hplatform : System.Platform.numBits ≤ 64 := by cases System.Platform.numBits_eq <;> omega
  have hdepthBound : depth.val + 1 ≤ Std.U32.max := by
    norm_num [U32.max, U32.numBits]
    omega
  obtain ⟨next, hnext, hnextVal⟩ := Aeneas.Std.WP.spec_imp_exists
    (U32.add_spec (x := depth) (y := 1#u32) (by simpa using hdepthBound))
  have hcast : (UScalar.cast .Usize depth).val = depth.val := by
    apply UScalar.cast_val_mod_pow_greater_numBits_eq
    simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
    cases System.Platform.numBits_eq <;> omega
  have hmachine : 64 ≤ Std.Usize.max := by
    rcases Usize.bounds_eq with h | h <;>
      norm_num [h, U32.max, U32.numBits, U64.max, U64.numBits]
  obtain ⟨binary, hbinary, hbinaryVal⟩ := Aeneas.Std.WP.spec_imp_exists
    (Usize.mul_spec (x := 2#usize) (y := UScalar.cast .Usize depth) (by simp [hcast]; omega))
  refine ⟨next, binary, hnext, ?_, ?_, ?_⟩
  · rw [ProgressiveTree.binary_depth_successor_eq ValueInst hnext]
    exact hbinary
  · simpa [hcast] using hbinaryVal
  · simp [hcast] at hbinaryVal
    omega

private theorem saturating_sub_val (index start : Std.Usize) :
    (core.num.Usize.saturating_sub index start).val = index.val - start.val := by
  change (index.val - start.val) % 2 ^ UScalarTy.Usize.numBits = index.val - start.val
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- Extracted lookup agrees with mathematical slots on a shaped spine whose
    layers have representable capacities. All arithmetic checks and routing
    shifts follow from those capacities. Indices before this suffix's start
    retain Rust's saturating-subtraction behavior. -/
theorem ProgressiveTree.get_recursive_eq_slot {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveTree T) (depth : Std.U32)
    (hshape : self.Shape factor depth.val) (hfits : self.Fits factor depth.val)
    (index : Std.Usize) :
    ProgressiveTree.get_recursive ValueInst self index depth =
      ok (self.slot factor depth.val (index.val - progressiveCapacity factor depth.val)) := by
  induction self generalizing depth with
  | ProgressiveZero => simp [ProgressiveTree.get_recursive, ProgressiveTree.slot]
  | ProgressiveNode hash left right ih =>
    cases hshape with
    | node _ hleft hright =>
      obtain ⟨hfit, hrightFit⟩ := hfits
      obtain ⟨next, binary, hnext, hbinary, hbinaryVal, hbits⟩ := next_layer_bounds ValueInst hlayout depth hfit
      have hnextVal : next.val = depth.val + 1 := by
        have h := UScalar.add_equiv depth 1#u32
        rw [hnext] at h
        simp at h
        omega
      obtain ⟨start, stop, hstart, hstop, hstartVal, hstopVal, _⟩ :=
        ProgressiveTree.layer_window ValueInst hlayout hnext hbinary (by simpa [hbinaryVal] using hfit)
      rw [hbinaryVal] at hstopVal
      have hpositive := hlayout.subtreeCapacity_pos (2 * depth.val)
      rw [ProgressiveTree.get_recursive]
      simp only [hnext, hstop, bind_tc_ok, ProgressiveTree.slot]
      by_cases hroute : index < stop
      · rw [if_pos hroute]
        have hlocal : index.val - progressiveCapacity factor depth.val < subtreeCapacity factor (2 * depth.val) := by
          have : index.val < stop.val := (UScalar.lt_equiv _ _).mp hroute
          omega
        rw [if_pos hlocal]
        simp only [hstart, hbinary, lift, bind_tc_ok, hlayout.opt_packing_depth_eq,
          hlayout.unwrap_opt_packing_depth_eq, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
        rw [hleft.get_recursive_eq_slot hlayout binary hbinaryVal (by omega)]
        rw [saturating_sub_val, hstartVal]
      · rw [if_neg hroute]
        have hlocal : ¬ index.val - progressiveCapacity factor depth.val < subtreeCapacity factor (2 * depth.val) := by
          have : ¬ index.val < stop.val := by simpa only [UScalar.lt_equiv] using hroute
          omega
        rw [if_neg hlocal]
        simp only [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok]
        rw [ih next (by simpa [hnextVal] using hright) (by simpa [hnextVal] using hrightFit)]
        simp only [hnextVal, progressiveCapacity_succ, Nat.sub_sub]

/-- A dense, bounded progressive spine implements sequence indexing at every
    machine index, including its missing suffix. No independent routing or
    successful-arithmetic assumptions are imposed. -/
theorem ProgressiveTree.Dense.get_recursive_eq_elements {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveTree T} {depth : Std.U32} {length : Nat}
    (hdense : self.Dense factor depth.val length) (hfits : self.Fits factor depth.val)
    (index : Std.Usize) :
    ProgressiveTree.get_recursive ValueInst self index depth =
      ok self.elements[index.val - progressiveCapacity factor depth.val]? := by
  rw [ProgressiveTree.get_recursive_eq_slot ValueInst hlayout self depth hdense.shape hfits index,
    hdense.slot_eq_elements]

end milhouse.progressive_tree
