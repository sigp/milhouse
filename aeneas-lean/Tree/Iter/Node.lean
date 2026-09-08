import Tree.Iter.Leaf

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

private theorem routing_div_iff {index shift shifted : Std.Usize}
    (hshift : index >>> shift = ok shifted) :
    (shifted &&& 1#usize) = 0#usize ↔ index.val / 2 ^ shift.val % 2 = 0 := by
  have hval := usize_shift_right_val hshift
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    simpa [hval, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using hv
  · intro h
    apply UScalar.eq_of_val_eq
    simpa [hval, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using h

/-- A live node frame descends to the selected child without changing the
    pending `next` result, its index, or cached geometry. The longer valid path
    decreases the remaining search depth, supplying recursive termination. -/
theorem Iter.next_node_step {T : Type} (ValueInst : Value T)
    {root : tree.Tree T} {depth packingDepth : Std.Usize} {factor : Option Std.Usize}
    {length : utils.Length} {self : Iter T}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hshape : root.Shape factor depth.val)
    (hbits : depth.val + packingDepth.val ≤ System.Platform.numBits)
    (hvalid : Iter.Valid root depth factor packingDepth length self)
    (completed : _root_.List (tree.Tree T))
    (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize))
    (left right : tree.Tree T)
    (hstack : self.stack.val = completed ++ [.Node hash left right])
    (hlive : self.index < length) :
    ∃ next, Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst next ∧
      next.index = self.index ∧ next.stack.val.length = self.stack.val.length + 1 ∧
      Iter.Valid root depth factor packingDepth length next := by
  obtain ⟨hdepth, hfactor, hpacking, hlength, hpath, _⟩ := hvalid
  have hpower : leafCapacity factor = 2 ^ packingDepth.val := by
    simpa [subtreeCapacity] using hlayout.subtreeCapacity_eq_two_pow 0
  have hpathTop : Path packingDepth.val root depth.val self.index.val
      (completed ++ [.Node hash left right]) := by simpa [hstack] using hpath
  obtain ⟨htop, _⟩ := hpathTop.top completed hpower hshape
  have hpositive : 0 < depth.val - completed.length := by
    generalize hremaining : depth.val - completed.length = remaining at htop
    cases htop
    omega
  have hstackLen : self.stack.val.length = completed.length + 1 := by simp [hstack]
  have hlen : (alloc.vec.Vec.len self.stack).val = self.stack.val.length := rfl
  have hstackBound : self.stack.val.length ≤ depth.val := by omega
  obtain ⟨childDepth, hsub, hsubVal, _⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := self.full_depth) (y := alloc.vec.Vec.len self.stack)
      (by simpa [hdepth, hlen] using hstackBound))
  have hchild : childDepth.val = depth.val - self.stack.val.length := by simpa [hdepth, hlen] using hsubVal
  have hshiftBound : childDepth.val + self.packing_depth.val < System.Platform.numBits := by
    rw [hpacking]
    omega
  obtain ⟨shift, hadd, haddVal⟩ := usize_add_succeeds (x := childDepth) (y := self.packing_depth)
    (by have hb : System.Platform.numBits < 2 ^ System.Platform.numBits := Nat.lt_two_pow_self; omega)
  obtain ⟨shifted, hshift, _⟩ := usize_shift_right_succeeds self.index (by omega : shift.val < System.Platform.numBits)
  have hroute := routing_div_iff hshift
  have hshiftVal : shift.val = childDepth.val + packingDepth.val := by simpa [hpacking] using haddVal
  have hparent : depth.val - completed.length = childDepth.val + 1 := by omega
  have hroom : self.stack.val.length < Usize.max := by
    have hword := System.Platform.numBits_le
    have hmax : 64 < Usize.max := by scalar_tac
    omega
  obtain ⟨rest, hpop, hrestore⟩ := vec_pop_push_same self.stack completed (.Node hash left right) hstack
  have hliveSelf : self.index < self.length := by simpa [hlength] using hlive
  by_cases hbit : (shifted &&& 1#usize) = 0#usize
  · obtain ⟨stack, hpush, hvalues⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec self.stack left hroom)
    refine ⟨{ self with stack }, ?_, rfl, by simp [hvalues], ?_⟩
    · rw [Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
      simp! only [utils.Length.as_usize, bind_tc_ok, if_neg (not_le_of_gt hliveSelf), hpop,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch, hrestore, hsub, hadd, hshift,
        lift, if_pos hbit, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hpush]
    · refine ⟨hdepth, hfactor, hpacking, hlength, ?_, ?_⟩
      · have htail : Path packingDepth.val (.Node hash left right)
            (depth.val - completed.length) self.index.val [.Node hash left right, left] := by
          rw [hparent]
          exact .left hash (by simpa [hshiftVal] using hroute.mp hbit) (.stop _ _ _)
        have hfull := hpathTop.extend completed [.Node hash left right, left] htail
        simpa [hvalues, hstack, _root_.List.append_assoc] using hfull
      · intro _
        simp [hvalues]
  · obtain ⟨stack, hpush, hvalues⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec self.stack right hroom)
    refine ⟨{ self with stack }, ?_, rfl, by simp [hvalues], ?_⟩
    · rw [Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
      simp! only [utils.Length.as_usize, bind_tc_ok, if_neg (not_le_of_gt hliveSelf), hpop,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch, hrestore, hsub, hadd, hshift,
        lift, if_neg hbit, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hpush]
    · refine ⟨hdepth, hfactor, hpacking, hlength, ?_, ?_⟩
      · have htail : Path packingDepth.val (.Node hash left right)
            (depth.val - completed.length) self.index.val [.Node hash left right, right] := by
          rw [hparent]
          exact .right hash (by simpa [hshiftVal] using (fun h => hbit (hroute.mpr h))) (.stop _ _ _)
        have hfull := hpathTop.extend completed [.Node hash left right, right] htail
        simpa [hvalues, hstack, _root_.List.append_assoc] using hfull
      · intro _
        simp [hvalues]

end milhouse.iter
