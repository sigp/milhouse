import Tree.Rebase.Arithmetic
import Tree.Rebase.Comparisons

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Successful checked splitting and both selected child calls suffice for
the actual ordered action combination. -/
theorem rebaseChildren_success {T : Type} (ValueInst : Value T)
    (origHash baseHash : alloy_primitives.bits.fixed.FixedBytes 32#usize)
    (origLeft origRight baseLeft baseRight : Tree T)
    (lengths : Option (utils.Length × utils.Length)) (fullDepth newDepth : Std.Usize)
    (hdepth : fullDepth - 1#usize = ok newDepth)
    (hshift : lengths.isSome = true → newDepth.val < UScalarTy.Usize.numBits)
    (hleft : ∀ childLengths,
      rebaseLengths childLengths = rebaseLeftLengths (rebaseLengths lengths) newDepth.val → ∃ action,
      Tree.rebase_on ValueInst origLeft baseLeft childLengths newDepth = ok (.Ok action))
    (hright : ∀ childLengths,
      rebaseLengths childLengths = rebaseRightLengths (rebaseLengths lengths) newDepth.val → ∃ action,
      Tree.rebase_on ValueInst origRight baseRight childLengths newDepth = ok (.Ok action)) :
    ∃ action, rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
      lengths fullDepth = ok (.Ok action) := by
  cases lengths with
  | none =>
    obtain ⟨leftAction, hleft⟩ := hleft none rfl
    obtain ⟨rightAction, hright⟩ := hright none rfl
    refine ⟨combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight leftAction rightAction, ?_⟩
    cases leftAction <;> cases rightAction <;>
      simp! [rebaseChildren, hdepth, core.option.Option.map, core.option.OptionPair.unzip,
        hleft, hright, core.result.Result.Insts.CoreOpsTry.branch, combineRebaseActions]
  | some lengths =>
    obtain ⟨origLength, baseLength⟩ := lengths
    obtain ⟨ol, bl, or, br, hsplit, _⟩ :=
      rebase_split_lengths_success ValueInst origLength baseLength newDepth (hshift rfl)
    have hinputs := rebase_split_comparison_inputs ValueInst hsplit
    obtain ⟨leftAction, hleft⟩ := hleft (some (ol, bl)) hinputs.1
    obtain ⟨rightAction, hright⟩ := hright (some (or, br)) hinputs.2
    refine ⟨combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight leftAction rightAction, ?_⟩
    cases leftAction <;> cases rightAction <;>
      simp! [rebaseChildren, hdepth, core.option.Option.map, core.option.OptionPair.unzip,
        hsplit, hleft, hright, core.result.Result.Insts.CoreOpsTry.branch, combineRebaseActions]

private theorem rebase_success_aux {T : Type} (ValueInst : Value T) :
    ∀ (n : Nat) (orig base : Tree T) (factor : Option Std.Usize) (depth : Nat)
      (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize),
      fullDepth.val ≤ n → orig.Shape factor depth → base.Shape factor depth →
      depth ≤ fullDepth.val → (lengths.isSome = true → fullDepth.val ≤ UScalarTy.Usize.numBits) →
      orig.RebaseComparisons ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val →
      ∃ action, Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro orig base factor depth lengths fullDepth hmeasure horig hbase hdepth hbits hcompare
    rw [Tree.rebase_on]
    obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec orig base
    clear hsame
    rw [hpointer]
    cases same with
    | true => exact ⟨.EqualNoop, rfl⟩
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
      cases orig <;> cases base <;> simp only
      case Leaf.Leaf left right =>
        obtain ⟨equal, hequal⟩ := milhouse_models.arc_eq_success ValueInst.corecmpPartialEqInst
          left.value right.value (hcompare hpointer)
        cases equal <;> simp [hequal]
      case PackedLeaf.PackedLeaf left right =>
        obtain ⟨equal, hequal⟩ := milhouse_models.vec_eq_success ValueInst.corecmpPartialEqInst
          left.values right.values (hcompare hpointer)
        cases equal <;> simp [hequal]
      case Zero.Zero left right =>
        simp only [lift, bind_tc_ok]
        split <;> simp
      case Node.Node origHash origLeft origRight baseHash baseLeft baseRight =>
        cases horig with
        | @node _ _ _ child _ origLeftShape origRightShape =>
          cases hbase with
          | node _ baseLeftShape baseRightShape =>
            have hpositive : fullDepth > 0#usize := by scalar_tac
            obtain ⟨newDepth, hnewDepth, hnewDepthVal⟩ :=
              usize_sub_one_succeeds (show 0 < fullDepth.val by omega)
            have hsmaller : newDepth.val < n := by omega
            have hchildDepth : child ≤ newDepth.val := by omega
            have hnewDepthNat : newDepth.val = fullDepth.val - 1 := by omega
            have hchildren (hdescend : ¬ RebaseHashShortcutFor origHash baseHash (rebaseLengths lengths)) :=
              rebaseChildren_success ValueInst origHash baseHash
                origLeft origRight baseLeft baseRight lengths fullDepth newDepth hnewDepth
                (fun hsome => by have := hbits hsome; omega)
                (fun childLengths hselected => ih newDepth.val hsmaller origLeft baseLeft factor child childLengths newDepth
                  (Nat.le_refl _) origLeftShape baseLeftShape hchildDepth
                  (fun hchildSome => by
                    have hsome : childLengths.isSome = lengths.isSome := by
                      have := congrArg Option.isSome hselected
                      simpa [rebaseLengths, rebaseLeftLengths] using this
                    have := hbits (hsome ▸ hchildSome)
                    omega)
                  (by
                    rw [hselected, hnewDepthNat]
                    exact (hcompare hpointer (by omega) hdescend).1))
                (fun childLengths hselected => ih newDepth.val hsmaller origRight baseRight factor child childLengths newDepth
                  (Nat.le_refl _) origRightShape baseRightShape hchildDepth
                  (fun hchildSome => by
                    have hsome : childLengths.isSome = lengths.isSome := by
                      have := congrArg Option.isSome hselected
                      simpa [rebaseLengths, rebaseRightLengths] using this
                    have := hbits (hsome ▸ hchildSome)
                    omega)
                  (by
                    rw [hselected, hnewDepthNat]
                    exact (hcompare hpointer (by omega) hdescend).2))
            rw [if_pos hpositive]
            simp only [lock_api.rwlock.RwLock.read,
              lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
              alloy_primitives.bits.fixed.FixedBytes.is_zero,
              alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
              lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
              triomphe.arc.Arc.new, bind_tc_ok, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
            split
            · rename_i hzero
              exact hchildren (fun hshortcut => hshortcut.1 hzero)
            · split
              · cases lengths with
                | none => simp [core.option.Option.is_none_or]
                | some lengths =>
                  rcases lengths with ⟨origLength, baseLength⟩
                  simp! only [core.option.Option.is_none_or,
                    Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                    utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq]
                  split
                  · simp
                  · rename_i hlengthNe
                    exact hchildren (fun hshortcut => hlengthNe (UScalar.eq_of_val_eq hshortcut.2.2))
              · rename_i hhashNe
                exact hchildren (fun hshortcut => hhashNe hshortcut.2.1)
      all_goals first
        | exact ⟨.NotEqualNoop, rfl⟩
        | (cases horig <;> cases hbase)

/-- Binary rebasing terminates for compatible tree shapes and total
comparisons at corresponding leaf positions. The depth bound is the checked
shift bound and is needed only when lengths are supplied. No packing queries,
density, length consistency, clone law, or
hash correctness is needed to obtain a successful action. -/
theorem Tree.rebase_on_success {T : Type} (ValueInst : Value T)
    (orig base : Tree T) {factor : Option Std.Usize} {depth : Nat}
    (horig : orig.Shape factor depth) (hbase : base.Shape factor depth)
    (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize)
    (hdepth : depth ≤ fullDepth.val)
    (hbits : lengths.isSome = true → fullDepth.val ≤ UScalarTy.Usize.numBits)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base
      (rebaseLengths lengths) fullDepth.val) :
    ∃ action, Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action) :=
  rebase_success_aux ValueInst fullDepth.val orig base factor depth lengths fullDepth (Nat.le_refl _)
    horig hbase hdepth hbits hcompare

end milhouse.tree
