import Tree.Builder.Finish.PackedMerge

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- Finishing a partial packed leaf succeeds and normalizes the builder's
forest. Its physical length rounds up to the packing boundary while its
logical length and all configuration fields stay unchanged. -/
theorem Builder.finish_packed_leaf_success {T : Type} {ValueInst : Value T}
    (self : Builder T) (hinvariant : BuilderInvariant ValueInst self)
    (hlevel : self.level.val = 0)
    (hpartial : self.length.val % subtreeCapacity self.packing_factor 0 ≠ 0) :
    ∃ forest, Builder.finish_packed_leaf ValueInst self self.length =
      ok (core.result.Result.Ok (), { self with stack := forest }) ∧
      BuilderNormalizedStack self.packing_factor 0 forest.val self.depth.val self.length.val
        (self.length.val + subtreeCapacity self.packing_factor 0 -
          self.length.val % subtreeCapacity self.packing_factor 0) := by
  have hlayout := BuilderInvariant.layout hinvariant
  have hstack : BuilderStack self.packing_factor 0 self.stack.val self.depth.val self.length.val := by
    simpa only [hlevel, ↓reduceIte] using BuilderInvariant.stack_dense hinvariant
  obtain ⟨prefixStack, top, topLen, hentries, htop, hpositive, htopPartial⟩ :=
    BuilderInvariant.partial_leaf hinvariant hlevel hpartial
  obtain ⟨prefixLen, hlength, haligned, hprefix⟩ :=
    hstack.remove_partial_last hlayout hentries htop hpositive htopPartial
  obtain ⟨count, finalStack, finalTop, finalDepth, finalLen, hplan, hcarry,
      _, hnormalized, _⟩ := hprefix.append_subtree hlayout htop hpositive haligned
    (by have hfits := hstack.length_le_capacity; omega)
  have hbits := hcarry.finish_partial_merge_bits hlayout hlength htopPartial
  obtain ⟨forest, hloop, hforest⟩ := Builder.finish_packed_leaf_loop_success hplan self
    self.length 0#usize hbits (BuilderInvariant.depth_packing_lt_bits hinvariant) hentries
  refine ⟨forest, ?_, ?_⟩
  · simp! only [Builder.finish_packed_leaf, hloop, bind_tc_ok]
  · have hrem : self.length.val % subtreeCapacity self.packing_factor 0 = topLen := by
      rw [hlength, Nat.add_mod, haligned, Nat.mod_eq_of_lt htopPartial]
      simp only [Nat.zero_add, Nat.mod_eq_of_lt htopPartial]
    have hphysical : prefixLen + subtreeCapacity self.packing_factor 0 =
        self.length.val + subtreeCapacity self.packing_factor 0 -
          self.length.val % subtreeCapacity self.packing_factor 0 := by
      rw [hrem]
      omega
    rw [hforest, ← hphysical, hlength]
    exact hnormalized

end milhouse.builder
