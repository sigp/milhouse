import Tree.Builder.New
import Tree.ProgressiveTree.Builder.Invariant

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- The initial progressive layer always has a representable capacity under
a valid packing layout, so builder creation succeeds without a depth premise. -/
theorem ProgressiveTreeBuilder.new_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) :
    ∃ self, ProgressiveTreeBuilder.new ValueInst = ok (core.result.Result.Ok self) := by
  have hnext : (0#u32) + 1#u32 = ok 1#u32 := rfl
  have hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst 1#u32 = ok 0#usize := by
    rw [ProgressiveTree.binary_depth_successor_eq ValueInst hnext]
    have hzero : UScalar.cast .Usize (0#u32) = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp
    rw [hzero]
    obtain ⟨product, hmul, hval⟩ := WP.spec_imp_exists
      (UScalar.mul_spec (x := 2#usize) (y := 0#usize) (by simp))
    have heq : product = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hval
    simpa only [heq] using hmul
  have hbound : subtreeCapacity factor (0#usize).val ≤ Std.Usize.max := by
    cases factor <;> simp only [subtreeCapacity, leafCapacity, show (0#usize).val = 0 from rfl,
      pow_zero, Nat.mul_one] <;> scalar_tac
  obtain ⟨current, hcurrent⟩ := Builder.new_success ValueInst hlayout 0#usize 0#usize hbound
  obtain ⟨capacity, hcapacity, _⟩ := ProgressiveTree.capacity_successor_eq ValueInst
    hlayout.opt_packing_factor_eq hnext
  refine ⟨{ subtrees := alloc.vec.Vec.new (triomphe.arc.Arc (tree.Tree T))
            current := current
            prog_depth := 1#u32
            capacity := capacity
            count := 0#usize
            length := 0#usize }, ?_⟩
  simp only [ProgressiveTreeBuilder.new, hbinary, hcurrent, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch, hcapacity]

/-- Total initialization establishes the complete geometry and counters and
an empty value sequence, using only the element packing layout. -/
theorem ProgressiveTreeBuilder.new_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) :
    ∃ self, ProgressiveTreeBuilder.new ValueInst = ok (core.result.Result.Ok self) ∧
      self.Valid ValueInst factor ∧ self.elements = [] ∧ self.length.val = 0 := by
  obtain ⟨self, hnew⟩ := ProgressiveTreeBuilder.new_success ValueInst hlayout
  obtain ⟨helements, hcounts⟩ := ProgressiveTreeBuilder.new_elements ValueInst hnew
  exact ⟨self, hnew, ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew, helements,
    by simpa only [helements, _root_.List.length_nil] using hcounts.2⟩

end milhouse.progressive_tree
