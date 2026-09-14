import Tree.ProgressiveTree.Builder.Push
import Tree.ProgressiveTree.LengthFits

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- A bound on the resulting sequence supplies exactly the next-layer bound
needed on rollover. All earlier layers and counter bounds follow from validity. -/
theorem ProgressiveTreeBuilder.push_length_fits_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T)
    (hvalid : self.Valid ValueInst factor)
    (hfits : ProgressiveTree.LengthFits factor (self.length.val + 1)) (value : T) :
    ∃ result, ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result) ∧ result.Valid ValueInst factor ∧
      result.elements = self.elements ++ [value] ∧ result.length.val = self.length.val + 1 := by
  apply ProgressiveTreeBuilder.push_spec ValueInst self hvalid ?_ value
  intro hfull
  obtain ⟨hcurrent, hfactor, _, hbinary, hprogressive, hcapacity, _⟩ := hvalid.1
  have hstart : progressiveCapacity factor self.prog_depth.val = self.length.val := by
    rw [hprogressive, progressiveCapacity_succ, hvalid.length_eq_layer_start_add_count,
      hfull, hcapacity, BuilderInvariant.builder_capacity_matches hcurrent, hfactor, hbinary]
  exact hfits self.prog_depth.val (by rw [hstart]; omega)

end milhouse.progressive_tree
