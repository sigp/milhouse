import Tree.ProgressiveTree.Geometry

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

theorem usize_saturating_sub_val (length start : Std.Usize) :
    (core.num.Usize.saturating_sub length start).val = length.val - start.val := by
  change (length.val - start.val) % 2 ^ UScalarTy.Usize.numBits = length.val - start.val
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- The rebasing calculation supplies the exact dense length of one binary
    layer. Representability of that layer removes capacity clamping and gives
    the global start; callers need no separate arithmetic assumptions. -/
theorem ProgressiveTree.rebase_layer_length {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {depth next : Std.U32} {start capacity binary length localLength : Std.Usize}
    (hfit : subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hnext : depth + 1#u32 = ok next)
    (hcapacity : ProgressiveTree.capacity_at_depth ValueInst next = ok capacity)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hmin : core.cmp.Ord.min.trait_default core.cmp.OrdUsize
      (core.num.Usize.saturating_sub length start) capacity = ok localLength) :
    localLength.val = min (length.val - progressiveCapacity factor depth.val)
      (subtreeCapacity factor (2 * depth.val)) := by
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  obtain ⟨actualStart, stop, hactualStart, _, hstartVal, _, _⟩ :=
    ProgressiveTree.layer_window ValueInst hlayout hnext hbinary (by simpa only [hbinaryVal] using hfit)
  rw [hstart] at hactualStart
  cases hactualStart
  obtain ⟨actualCapacity, hactualCapacity, hcapacityVal⟩ :=
    ProgressiveTree.capacity_successor_eq ValueInst hlayout.opt_packing_factor_eq hnext
  rw [hcapacity] at hactualCapacity
  cases hactualCapacity
  rw [min_eq_right (by scalar_tac)] at hcapacityVal
  obtain ⟨actualMin, hactualMin, hminVal⟩ := Aeneas.Std.WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_Usize.spec (core.num.Usize.saturating_sub length start) capacity)
  rw [hmin] at hactualMin
  cases hactualMin
  rw [hminVal, core.cmp.impls.OrdUsize.min_val, usize_saturating_sub_val, hstartVal, hcapacityVal]

end milhouse.progressive_tree
