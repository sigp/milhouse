import Tree.Rebase.Success
import Tree.Rebase.ComparisonReflection

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- When the supplied metadata selects descent, a successful node result
comes from the actual two-child computation. No shape, density, cache law,
or bound beyond the selected positive-depth guard is assumed. -/
theorem Tree.rebase_on_children_of_descend {T : Type} (ValueInst : Value T)
    {origHash baseHash : CacheHash} {origLeft origRight baseLeft baseRight : Tree T}
    {lengths : Option (utils.Length × utils.Length)} {fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node origHash origLeft origRight : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hpositive : fullDepth > 0#usize)
    (hdescend : ¬ RebaseHashShortcutFor origHash baseHash (rebaseLengths lengths))
    (hrebase : Tree.rebase_on ValueInst (.Node origHash origLeft origRight)
      (.Node baseHash baseLeft baseRight) lengths fullDepth = ok (.Ok action)) :
    rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
      lengths fullDepth = ok (.Ok action) := by
  rw [Tree.rebase_on, hpointer] at hrebase
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_pos hpositive,
    lock_api.rwlock.RwLock.read,
    lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
    alloy_primitives.bits.fixed.FixedBytes.is_zero,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
    lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
    triomphe.arc.Arc.new, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hrebase
  split at hrebase
  · exact hrebase
  · rename_i hnonzero
    split at hrebase
    · rename_i hhash
      cases lengths with
      | none => exact (hdescend ⟨hnonzero, hhash, trivial⟩).elim
      | some pair =>
        obtain ⟨origLength, baseLength⟩ := pair
        simp! only [core.option.Option.is_none_or,
          Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
          utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
        split at hrebase
        · rename_i hlength
          exact (hdescend ⟨hnonzero, hhash, congrArg UScalar.val hlength⟩).elim
        · exact hrebase
    · exact hrebase

/-- Every successful binary rebase supplies exactly the selected element
termination law at its actual optional lengths and full depth. This direction
requires no input geometry, metadata accuracy, equality soundness, or cache
validity. In particular, missing lengths stay missing through recursion. -/
theorem Tree.rebase_on_comparisons {T : Type} (ValueInst : Value T)
    {orig base : Tree T} {lengths : Option (utils.Length × utils.Length)}
    {fullDepth : Std.Usize} {action : RebaseAction (Tree T)}
    (hrebase : Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) :
    orig.RebaseComparisons ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val := by
  induction orig generalizing base lengths fullDepth action with
  | Leaf left =>
    cases base <;> simp only [Tree.RebaseComparisons]
    case Leaf right =>
      intro hpointer
      rw [Tree.rebase_on, hpointer] at hrebase
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      rw [bind_eq_ok_iff] at hrebase
      obtain ⟨equal, hcompare, _⟩ := hrebase
      exact milhouse_models.arc_comparisons_of_eq_success ValueInst.corecmpPartialEqInst hcompare
  | PackedLeaf left =>
    cases base <;> simp only [Tree.RebaseComparisons]
    case PackedLeaf right =>
      intro hpointer
      rw [Tree.rebase_on, hpointer] at hrebase
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      rw [bind_eq_ok_iff] at hrebase
      obtain ⟨equal, hcompare, _⟩ := hrebase
      exact milhouse_models.neComparisons_of_vec_eq_success ValueInst.corecmpPartialEqInst hcompare
  | Zero depth => cases base <;> trivial
  | Node origHash origLeft origRight ihleft ihright =>
    cases base <;> simp only [Tree.RebaseComparisons]
    case Node baseHash baseLeft baseRight =>
      intro hpointer hpositive hdescend
      have hchildren := Tree.rebase_on_children_of_descend ValueInst hpointer
        (by scalar_tac) hdescend hrebase
      obtain ⟨newDepth, mapped, leftLengths, rightLengths, leftAction, rightAction,
        hnewDepth, hmapped, hsplit, hleft, hright, _⟩ := rebaseChildren_success_state ValueInst hchildren
      have hnewDepthVal := usize_sub_one_val hnewDepth
      have hnewDepthNat : newDepth.val = fullDepth.val - 1 := by omega
      have hselected :
          rebaseLengths leftLengths = rebaseLeftLengths (rebaseLengths lengths) newDepth.val ∧
          rebaseLengths rightLengths = rebaseRightLengths (rebaseLengths lengths) newDepth.val := by
        cases lengths with
        | none =>
          simp only [core.option.Option.map, ok.injEq] at hmapped
          subst mapped
          simp only [core.option.OptionPair.unzip, ok.injEq, Prod.mk.injEq] at hsplit
          obtain ⟨rfl, rfl⟩ := hsplit
          exact ⟨rfl, rfl⟩
        | some pair =>
          obtain ⟨origLength, baseLength⟩ := pair
          simp only [core.option.Option.map] at hmapped
          rw [bind_eq_ok_iff] at hmapped
          obtain ⟨⟨⟨ol, bl⟩, or, br⟩, hlengthSplit, hmapped⟩ := hmapped
          simp only [ok.injEq] at hmapped
          subst mapped
          simp only [core.option.OptionPair.unzip, ok.injEq, Prod.mk.injEq] at hsplit
          obtain ⟨rfl, rfl⟩ := hsplit
          exact rebase_split_comparison_inputs ValueInst hlengthSplit
      constructor
      · simpa only [hselected.1, hnewDepthNat] using ihleft hleft
      · simpa only [hselected.2, hnewDepthNat] using ihright hright

/-- Under compatible shapes and the checked-depth bounds, successful binary
rebasing is equivalent to termination of only the reached element comparisons.
The criterion assumes no comparison success or semantic content law. -/
theorem Tree.rebase_on_success_iff {T : Type} (ValueInst : Value T)
    (orig base : Tree T) {factor : Option Std.Usize} {depth : Nat}
    (horig : orig.Shape factor depth) (hbase : base.Shape factor depth)
    (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize)
    (hdepth : depth ≤ fullDepth.val)
    (hbits : lengths.isSome = true → fullDepth.val ≤ UScalarTy.Usize.numBits) :
    (∃ action, Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) ↔
      orig.RebaseComparisons ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val := by
  constructor
  · rintro ⟨action, hrebase⟩
    exact Tree.rebase_on_comparisons ValueInst hrebase
  · exact Tree.rebase_on_success ValueInst orig base horig hbase lengths fullDepth hdepth hbits

end milhouse.tree
