import Tree.Builder.Contents.Push
import Tree.Builder.Contents.Finish

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

/-- **Sequence-level builder finalization.** A valid builder finishes with
    precisely its accumulated values, the correct depth and sequence length,
    and a dense output tree. The existing builder invariant supplies every
    structural and packing condition; none is imposed separately. -/
theorem Builder.finish_spec {T : Type} {ValueInst : Value T} {self : Builder T}
    (hinvariant : BuilderInvariant ValueInst self)
    {output : tree.Tree T} {depth : Std.Usize} {length : utils.Length}
    (hfinish : Builder.finish ValueInst self = ok (core.result.Result.Ok (output, depth, length))) :
    output.elements = self.elements ∧ depth = self.depth ∧ length.val = self.elements.length ∧
      DenseTree self.packing_factor output depth.val self.elements.length := by
  have hcontents := Builder.finish_elements ValueInst self hfinish
  obtain ⟨rfl, rfl, hdense⟩ := builder_finish_returns_dense hinvariant hfinish
  have hlength : self.elements.length = self.length.val := by
    rw [← hcontents]
    exact hdense.elements_length
  exact ⟨hcontents, rfl, hlength.symm, by simpa [hlength] using hdense⟩

/-- The finalized tree implements exact indexing of the builder's accumulated
    sequence at every position in its capacity, including the unused suffix.
    The builder invariant already supplies the lookup shift bound. -/
theorem Builder.finish_get_elements {T : Type} {ValueInst : Value T} {self : Builder T}
    (hinvariant : BuilderInvariant ValueInst self)
    {output : tree.Tree T} {depth : Std.Usize} {length : utils.Length}
    (hfinish : Builder.finish ValueInst self = ok (core.result.Result.Ok (output, depth, length)))
    (index : Std.Usize) (hindex : index.val < self.capacity.val) :
    tree.Tree.get_recursive ValueInst output index depth self.packing_depth =
      ok self.elements[index.val]? := by
  have hcontents := Builder.finish_elements ValueInst self hfinish
  obtain ⟨rfl, rfl, hdense⟩ := builder_finish_returns_dense hinvariant hfinish
  have hbits := hinvariant.depth_packing_lt_bits
  have hcapacity := @BuilderInvariant.builder_capacity_matches T ValueInst self hinvariant
  rw [hdense.get_recursive_eq_elements (@BuilderInvariant.layout T ValueInst self hinvariant)
    (by omega) index (by omega), hcontents]

end milhouse.builder
