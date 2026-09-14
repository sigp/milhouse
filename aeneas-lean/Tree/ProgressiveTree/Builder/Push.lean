import Tree.Builder.New
import Tree.Builder.Push.Success
import Tree.Builder.Finish.Full
import Tree.ProgressiveTree.Builder.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- A valid progressive builder accepts a value, including rollover of a full
current subtree. Only rollover needs a capacity bound for the new binary layer;
all counter, vector, depth, and carry bounds follow internally. -/
theorem ProgressiveTreeBuilder.push_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T)
    (hvalid : self.Valid ValueInst factor)
    (hnextFits : self.count = self.capacity →
      subtreeCapacity factor (2 * self.prog_depth.val) ≤ Std.Usize.max) (value : T) :
    ∃ result, ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result) := by
  obtain ⟨hcurrent, hfactor, hlevel, hbinaryDepth, hprogressive, hcapacity, hfullLayers⟩ := hvalid.1
  have hcount := hvalid.count_eq_current_length
  have hlengthBound : self.length.val + (1#usize).val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    have hroom := hvalid.length_lt_max
    change self.length.val + 1 ≤ Std.Usize.max
    omega
  obtain ⟨length, hlength, _⟩ := WP.spec_imp_exists (UScalar.add_spec hlengthBound)
  by_cases hfull : self.count = self.capacity
  · have hlayout := BuilderInvariant.layout hcurrent
    rw [hfactor] at hlayout
    have hmax : Std.Usize.max < 2 ^ System.Platform.numBits := by
      cases System.Platform.numBits_eq <;> simp_all [Std.Usize.max, Std.Usize.numBits]
    obtain ⟨depth, binary, hnext, hbinary, hbinaryVal, _⟩ := next_layer_bounds ValueInst
      hlayout self.prog_depth (lt_of_le_of_lt (hnextFits hfull) hmax)
    obtain ⟨empty, hnew, hempty, _, _, helevel, helength⟩ := Builder.new_spec ValueInst
      hlayout binary 0#usize (by simpa only [hbinaryVal] using hnextFits hfull)
      (Or.inl rfl) (by simp)
    have hcurrentFull : self.current.length = self.current.capacity :=
      hcount.symm.trans (hfull.trans hcapacity)
    obtain ⟨tree, hfinish⟩ := Builder.finish_full_success self.current hcurrent hlevel hcurrentFull
    have hvecRoom : self.subtrees.val.length < Std.Usize.max := by
      have hdepthMax : self.current.depth.val ≤ Std.Usize.max := by scalar_tac
      have hpositive : 0 < Std.Usize.max := by scalar_tac
      omega
    obtain ⟨subtrees, hsubtrees, _⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec self.subtrees tree hvecRoom)
    obtain ⟨capacity, hcached, _⟩ := ProgressiveTree.capacity_successor_eq ValueInst
      hlayout.opt_packing_factor_eq hnext
    have hspare : empty.length.val < empty.capacity.val := by
      rw [helength, BuilderInvariant.builder_capacity_matches hempty,
        (BuilderInvariant.layout hempty).subtreeCapacity_eq_two_pow]
      change 0 < 2 ^ _
      positivity
    obtain ⟨current, hpush⟩ := Builder.push_success empty hempty
      (by simp only [helevel]; rfl) hspare value
    obtain ⟨one, hone, honeVal⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
    have honeEq : one = 1#usize := by
      apply UScalar.eq_of_val_eq
      simpa using honeVal
    subst one
    refine ⟨{ subtrees, current, prog_depth := depth, capacity, count := 1#usize, length }, ?_⟩
    simp! only [ProgressiveTreeBuilder.push, hfull, ↓reduceIte, hnext, hbinary, hnew,
      bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, core.mem.replace, hfinish,
      hsubtrees, hcached, hpush, hone, hlength]
  · have hnotFull : self.current.length.val ≠ self.current.capacity.val := by
      intro h
      apply hfull
      apply UScalar.eq_of_val_eq
      simpa only [hcount, hcapacity] using h
    have hspare : self.current.length.val < self.current.capacity.val := by
      have hle := BuilderInvariant.length_le_capacity hcurrent
      omega
    obtain ⟨current, hpush⟩ := Builder.push_success self.current hcurrent hlevel hspare value
    have hcountBound : self.count.val + (1#usize).val ≤ UScalar.max .Usize := by
      rw [UScalar.max_USize_eq, hcount]
      have hcapMax : self.current.capacity.val ≤ Std.Usize.max := by scalar_tac
      change self.current.length.val + 1 ≤ Std.Usize.max
      omega
    obtain ⟨count, hcountAdd, _⟩ := WP.spec_imp_exists (UScalar.add_spec hcountBound)
    refine ⟨{ self with current, count, length }, ?_⟩
    simp! only [ProgressiveTreeBuilder.push, hfull, ↓reduceIte, hpush, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch, hcountAdd, hlength]

/-- Total progressive insertion appends exactly the supplied value, increments
the total length, and preserves the complete builder invariant. -/
theorem ProgressiveTreeBuilder.push_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} (self : ProgressiveTreeBuilder T)
    (hvalid : self.Valid ValueInst factor)
    (hnextFits : self.count = self.capacity →
      subtreeCapacity factor (2 * self.prog_depth.val) ≤ Std.Usize.max) (value : T) :
    ∃ result, ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result) ∧ result.Valid ValueInst factor ∧
      result.elements = self.elements ++ [value] ∧ result.length.val = self.length.val + 1 := by
  obtain ⟨result, hpush⟩ := ProgressiveTreeBuilder.push_success ValueInst self hvalid hnextFits value
  obtain ⟨helements, hlength, _⟩ := ProgressiveTreeBuilder.push_contents ValueInst self value hpush
  exact ⟨result, hpush, ProgressiveTreeBuilder.push_preserves_valid ValueInst hvalid value hpush,
    helements, hlength⟩

end milhouse.progressive_tree
