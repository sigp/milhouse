import Tree.ProgressiveTree.Geometry

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Successful capacity calculation has already obtained a packing factor.
This extracts the actual answer without a separate metadata-termination law. -/
theorem ProgressiveTree.packing_factor_of_total_capacity_success {T : Type}
    (ValueInst : Value T) {depth : Std.U32} {capacity : Std.Usize}
    (hcapacity : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok capacity) :
    ∃ factor, utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor := by
  unfold ProgressiveTree.total_capacity_at_depth at hcapacity
  simp only [lift, bind_tc_ok] at hcapacity
  rw [bind_eq_ok_iff] at hcapacity
  obtain ⟨power, _, hcapacity⟩ := hcapacity
  rw [bind_eq_ok_iff] at hcapacity
  obtain ⟨denominator, _, hcapacity⟩ := hcapacity
  rw [bind_eq_ok_iff] at hcapacity
  obtain ⟨quotient, _, hcapacity⟩ := hcapacity
  rw [bind_eq_ok_iff] at hcapacity
  obtain ⟨factor, hfactor, _⟩ := hcapacity
  exact ⟨factor, hfactor⟩

/-- Successful capacities are monotone in progressive depth, including
saturation and arbitrary packing-factor answers. -/
theorem ProgressiveTree.total_capacity_success_mono {T : Type}
    (ValueInst : Value T) {left right : Std.U32} {lo hi : Std.Usize}
    (hleft : ProgressiveTree.total_capacity_at_depth ValueInst left = ok lo)
    (hright : ProgressiveTree.total_capacity_at_depth ValueInst right = ok hi)
    (hdepth : left.val ≤ right.val) : lo.val ≤ hi.val := by
  obtain ⟨factor, hfactor⟩ := ProgressiveTree.packing_factor_of_total_capacity_success ValueInst hleft
  obtain ⟨actualLo, hactualLo, hlo⟩ := ProgressiveTree.total_capacity_eq ValueInst hfactor left
  obtain ⟨actualHi, hactualHi, hhi⟩ := ProgressiveTree.total_capacity_eq ValueInst hfactor right
  rw [hleft] at hactualLo
  cases hactualLo
  rw [hright] at hactualHi
  cases hactualHi
  have hmono := progressiveCapacity_mono factor hdepth
  omega

end milhouse.progressive_tree
