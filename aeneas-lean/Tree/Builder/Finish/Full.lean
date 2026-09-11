import Tree.Builder.Carry
import Tree.Builder.Contents.Finish

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.builder

private theorem shift_left_zero (value : Std.Usize) : value <<< (0#usize) = ok value := by
  change UScalar.shiftLeft value 0 = ok value
  rw [UScalar.shiftLeft, if_pos (Nat.pos_of_ne_zero (UScalarTy.numBits_nonzero .Usize))]
  change ok ({ bv := value.bv <<< (0 : Nat) } : Std.Usize) = ok value
  rw [BitVec.shiftLeft_zero]

private theorem div_ceil_one (value : Std.Usize) :
    core.num.Usize.div_ceil value 1#usize = ok value := by
  simp only [core.num.Usize.div_ceil, show (1#usize).val = 1 from rfl, Nat.one_ne_zero,
    ↓reduceIte, Nat.div_one, Nat.mod_one, Nat.add_zero,
    UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, value.hBounds, decide_true,
    ↓reduceDIte, Result.ofOption]
  congr 1

private theorem saturating_sub_zero (value : Std.Usize) :
    core.num.Usize.saturating_sub value 0#usize = value := by
  apply UScalar.eq_of_val_eq
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val,
    BitVec.toNat_ofNat]
  change max 0 (value.val - 0) % 2 ^ UScalarTy.Usize.numBits = value.val
  rw [Nat.sub_zero, max_eq_right (Nat.zero_le _), Nat.mod_eq_of_lt value.hBounds]

private theorem remainder_zero (value factor : Std.Usize) (hfactor : 0 < factor.val)
    (haligned : value.val % factor.val = 0) : value % factor = ok 0#usize := by
  obtain ⟨remainder, hrem, hval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec value (y := factor) (by omega))
  have heq : remainder = 0#usize := by
    apply UScalar.eq_of_val_eq
    simpa only [haligned, show (0#usize).val = 0 from rfl] using hval
  simpa only [heq] using hrem

/-- A full leaf-level builder has already merged to one root and needs no
padding. Finalization therefore succeeds and returns that root unchanged. -/
theorem Builder.finish_full_success {T : Type} {ValueInst : Value T}
    (self : Builder T) (hinvariant : BuilderInvariant ValueInst self)
    (hlevel : self.level.val = 0) (hfull : self.length = self.capacity) :
    ∃ tree, Builder.finish ValueInst self =
      ok (core.result.Result.Ok (tree, self.depth, self.length)) := by
  have hlayout := BuilderInvariant.layout hinvariant
  have hcapacity := BuilderInvariant.builder_capacity_matches hinvariant
  obtain ⟨entry, hstack, _⟩ := (BuilderInvariant.stack_dense hinvariant).full_single hlayout
    (by rw [hfull, hcapacity])
  have hlevelEq : self.level = 0#usize := UScalar.eq_of_val_eq hlevel
  have hempty : alloc.vec.Vec.is_empty Global self.stack = ok false := by
    simp [alloc.vec.Vec.is_empty, hstack]
  obtain ⟨rest, hpop, hrest⟩ := vec_pop_append_last (A := Global) self.stack [] entry hstack
  have hrestEmpty : alloc.vec.Vec.is_empty Global rest = ok true := by
    simp [alloc.vec.Vec.is_empty, hrest]
  have hshift : self.length <<< self.level = ok self.capacity := by
    rw [hlevelEq, shift_left_zero, hfull]
  have hbody : Builder.finish_tree_loop.body ValueInst self self.length =
      ok (.done (core.result.Result.Ok (), self)) := by
    simp only [Builder.finish_tree_loop.body, hshift, bind_tc_ok, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte]
  have hfinishTree : Builder.finish_tree ValueInst self self.length =
      ok (core.result.Result.Ok (), self) := by
    rw [Builder.finish_tree, Builder.finish_tree_loop, loop]
    simp! only [hbody, bind_tc_ok]
  have hlevelCapacity : (1#usize) <<< self.level = ok 1#usize := by
    rw [hlevelEq, shift_left_zero]
  refine ⟨maybeArcedTree entry, ?_⟩
  cases hfactor : self.packing_factor with
  | none =>
    simp! only [Builder.finish, hempty, Bool.false_eq_true, ↓reduceIte,
      utils.Length.as_usize, bind_tc_ok, hlevelCapacity, div_ceil_one, hfactor,
      hfinishTree, core.result.Result.Insts.CoreOpsTry.branch, hpop,
      core.option.Option.ok_or, maybeArced_arced, hrestEmpty]
  | some factor =>
    rw [hfactor] at hlayout hcapacity
    have hpositive : 0 < factor.val := by simpa only [leafCapacity] using hlayout.leafCapacity_pos
    have haligned : self.length.val % factor.val = 0 := by
      rw [hfull, hcapacity]
      simp [subtreeCapacity, leafCapacity]
    have hrem := remainder_zero self.length factor hpositive haligned
    have hskip := remainder_zero factor factor hpositive (Nat.mod_self _)
    simp! only [Builder.finish, hempty, Bool.false_eq_true, ↓reduceIte,
      utils.Length.as_usize, bind_tc_ok, hlevelCapacity, div_ceil_one, hfactor,
      hrem, lift, saturating_sub_zero, hskip, lt_self_iff_false, ↓reduceIte,
      hfinishTree, core.result.Result.Insts.CoreOpsTry.branch, hpop,
      core.option.Option.ok_or, maybeArced_arced, hrestEmpty]

end milhouse.builder
