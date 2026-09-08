import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

/-- A packed leaf with spare capacity accepts the supplied value without
calling its clone implementation. Its machine bound follows from the factor. -/
theorem PackedLeaf.push_success {T : Type}
    (hashInst : tree_hash.TreeHash T) (cloneInst : core.clone.Clone T)
    (self : PackedLeaf T) (value : T) (factor : Std.Usize)
    (hfactor : hashInst.tree_hash_packing_factor = ok factor)
    (hspare : self.values.val.length < factor.val) :
    ∃ result, PackedLeaf.push hashInst cloneInst self value =
      ok (core.result.Result.Ok (), result) ∧
      result.values.val = self.values.val ++ [value] := by
  have hroom : self.values.val.length < Std.Usize.max := by
    have hf : factor.val ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨values, hpush, hvalues⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec self.values value hroom)
  have hne : self.values.len ≠ factor := by
    intro h
    have hlen := congrArg UScalar.val h
    simp only [alloc.vec.Vec.len_val] at hlen
    change self.values.val.length = factor.val at hlen
    omega
  refine ⟨{ self with values }, ?_, hvalues⟩
  simp only [PackedLeaf.push, hfactor, hne, ↓reduceIte, bind_tc_ok, hpush]

end milhouse.packed_leaf
