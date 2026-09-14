import Tree.Builder.Contents.Length
import Tree.ProgressiveTree.Builder.Invariant

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- The progressive counter agrees with the current binary builder's counter
directly from validity, without assuming any successful finalization. -/
theorem ProgressiveTreeBuilder.Valid.count_eq_current_length {T : Type}
    {ValueInst : Value T} {factor : Option Std.Usize} {self : ProgressiveTreeBuilder T}
    (hvalid : self.Valid ValueInst factor) : self.count = self.current.length := by
  apply UScalar.eq_of_val_eq
  exact hvalid.2.1.trans (BuilderInvariant.elements_length
    (@ProgressiveTreeBuilder.Geometry.current T ValueInst factor self hvalid.1))

/-- The total length consists of the full progressive prefix and the current
layer's count. -/
theorem ProgressiveTreeBuilder.Valid.length_eq_layer_start_add_count {T : Type}
    {ValueInst : Value T} {factor : Option Std.Usize} {self : ProgressiveTreeBuilder T}
    (hvalid : self.Valid ValueInst factor) :
    self.length.val = progressiveCapacity factor self.subtrees.val.length + self.count.val := by
  have hfull := (@ProgressiveTreeBuilder.Geometry.completed T ValueInst factor self hvalid.1).elements_length
  simp only [progressiveCapacity_zero, Nat.zero_add] at hfull
  rw [hvalid.2.2, ProgressiveTreeBuilder.elements, _root_.List.length_append,
    hfull, hvalid.2.1]

/-- Every valid progressive builder has room to increment its total counter.
The full preceding layers occupy only one third of the current layer, whose
power-of-two capacity is itself representable. Rollover may still require a
separate representability bound for the next binary layer. -/
theorem ProgressiveTreeBuilder.Valid.length_lt_max {T : Type}
    {ValueInst : Value T} {factor : Option Std.Usize} {self : ProgressiveTreeBuilder T}
    (hvalid : self.Valid ValueInst factor) : self.length.val < Std.Usize.max := by
  obtain ⟨hcurrent, hfactor, hlevel, hbinary, hprogressive, hcapacity, hfull⟩ := hvalid.1
  have hlayout := BuilderInvariant.layout hcurrent
  have hcap := BuilderInvariant.builder_capacity_matches hcurrent
  have hbits := BuilderInvariant.depth_packing_lt_bits hcurrent
  have hcount := BuilderInvariant.length_le_capacity hcurrent
  rw [← hvalid.count_eq_current_length] at hcount
  have hlength := hvalid.length_eq_layer_start_add_count
  rw [← hfactor] at hlength
  have hrelation := progressiveCapacity_layer_relation factor self.subtrees.val.length
  have hpositive := hlayout.leafCapacity_pos
  rw [← hbinary, ← hfactor, ← hcap] at hrelation
  have hdouble : 2 * self.current.capacity.val ≤ 2 ^ System.Platform.numBits := by
    rw [hcap, hlayout.subtreeCapacity_eq_two_pow]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show self.current.packing_depth.val + self.current.depth.val + 1 ≤
        System.Platform.numBits by omega)
    simpa only [pow_succ, Nat.mul_comm] using hp
  have hmax : Std.Usize.max + 1 = 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all [Std.Usize.max, Std.Usize.numBits]
  have hlarge : 2 ≤ Std.Usize.max := by scalar_tac
  omega

end milhouse.progressive_tree
