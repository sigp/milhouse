import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

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
