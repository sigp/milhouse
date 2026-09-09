import Tree.Rebase.GeometryInputs
import Tree.Rebase.SuccessReflection

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Successful splitting entails precisely the checked shift's bound. -/
theorem rebase_split_shift_bound {T : Type} (ValueInst : Value T)
    {origLength baseLength newDepth ol bl or br : Std.Usize}
    (hsplit : Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once
      ValueInst newDepth (origLength, baseLength) = ok ((ol, bl), (or, br))) :
    newDepth.val < UScalarTy.Usize.numBits := by
  unfold Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once at hsplit
  dsimp! only at hsplit
  rw [bind_eq_ok_iff] at hsplit
  obtain ⟨capacity, hshift, _⟩ := hsplit
  change UScalar.shiftLeft 1#usize newDepth.val = ok capacity at hshift
  unfold UScalar.shiftLeft at hshift
  split at hshift
  · assumption
  · simp at hshift

/-- The actual child computation supplies both selected length inputs and
the optional shift bound, without assuming accurate lengths or any geometry. -/
theorem rebaseChildren_selected_inputs {T : Type} (ValueInst : Value T)
    {origHash baseHash : CacheHash} {origLeft origRight baseLeft baseRight : Tree T}
    {lengths : Option (utils.Length × utils.Length)} {fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hchildren : rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
      lengths fullDepth = ok (.Ok action)) :
    ∃ newDepth leftLengths rightLengths leftAction rightAction,
      newDepth.val = fullDepth.val - 1 ∧
      (lengths.isSome = true → newDepth.val < UScalarTy.Usize.numBits) ∧
      rebaseLengths leftLengths = rebaseLeftLengths (rebaseLengths lengths) newDepth.val ∧
      rebaseLengths rightLengths = rebaseRightLengths (rebaseLengths lengths) newDepth.val ∧
      Tree.rebase_on ValueInst origLeft baseLeft leftLengths newDepth = ok (.Ok leftAction) ∧
      Tree.rebase_on ValueInst origRight baseRight rightLengths newDepth = ok (.Ok rightAction) := by
  obtain ⟨newDepth, mapped, leftLengths, rightLengths, leftAction, rightAction,
    hdepth, hmapped, hsplit, hleft, hright, _⟩ := rebaseChildren_success_state ValueInst hchildren
  have hdepthVal := usize_sub_one_val hdepth
  refine ⟨newDepth, leftLengths, rightLengths, leftAction, rightAction, by omega, ?_, ?_, ?_, hleft, hright⟩
  all_goals
    cases lengths with
    | none =>
      simp only [core.option.Option.map, ok.injEq] at hmapped
      subst mapped
      simp only [core.option.OptionPair.unzip, ok.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      simp [rebaseLengths, rebaseLeftLengths, rebaseRightLengths]
    | some pair =>
      obtain ⟨origLength, baseLength⟩ := pair
      simp only [core.option.Option.map] at hmapped
      rw [bind_eq_ok_iff] at hmapped
      obtain ⟨⟨⟨ol, bl⟩, or, br⟩, hlengthSplit, hmapped⟩ := hmapped
      simp only [ok.injEq] at hmapped
      subst mapped
      simp only [core.option.OptionPair.unzip, ok.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      first
      | exact fun _ => rebase_split_shift_bound ValueInst hlengthSplit
      | exact (rebase_split_comparison_inputs ValueInst hlengthSplit).1
      | exact (rebase_split_comparison_inputs ValueInst hlengthSplit).2

/-- Successful binary rebasing entails its selected shape and arithmetic
checks. This reflection assumes no whole-tree invariant, packing law, accurate
metadata, element law, or hash-validity law. -/
theorem Tree.rebase_on_geometry {T : Type} (ValueInst : Value T)
    {orig base : Tree T} {lengths : Option (utils.Length × utils.Length)}
    {fullDepth : Std.Usize} {action : RebaseAction (Tree T)}
    (hrebase : Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) :
    orig.RebaseGeometry base (rebaseLengths lengths) fullDepth.val := by
  induction orig generalizing base lengths fullDepth action with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    cases base <;> simp only [Tree.RebaseGeometry]
    all_goals
      intro hpointer
      rw [Tree.rebase_on, hpointer] at hrebase
      simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseGeometry]
    case Leaf | PackedLeaf =>
      intro hpointer
      rw [Tree.rebase_on, hpointer] at hrebase
      simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
    case Node baseHash baseLeft baseRight =>
      intro hpointer
      have hpositive : fullDepth > 0#usize := by
        by_contra hzero
        rw [Tree.rebase_on, hpointer] at hrebase
        simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hzero] at hrebase
      refine ⟨by scalar_tac, fun hdescend => ?_⟩
      have hchildren := Tree.rebase_on_children_of_descend ValueInst hpointer hpositive hdescend hrebase
      obtain ⟨newDepth, leftLengths, rightLengths, leftAction, rightAction,
        hdepthVal, hshift, hleftLengths, hrightLengths, hleft, hright⟩ :=
        rebaseChildren_selected_inputs ValueInst hchildren
      refine ⟨?_, ?_, ?_⟩
      · simpa only [rebaseLengths, Option.isSome_map, hdepthVal] using hshift
      · simpa only [hleftLengths, hdepthVal] using ihleft hleft
      · simpa only [hrightLengths, hdepthVal] using ihright hright

private theorem success_of_geometry_aux {T : Type} (ValueInst : Value T) :
    ∀ (n : Nat) (orig base : Tree T) (lengths : Option (utils.Length × utils.Length))
      (fullDepth : Std.Usize), fullDepth.val ≤ n →
      orig.RebaseGeometry base (rebaseLengths lengths) fullDepth.val →
      orig.RebaseComparisons ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val →
      ∃ action, Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro orig base lengths fullDepth hmeasure hgeometry hcompare
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
        have hpositive : fullDepth > 0#usize := by have := (hgeometry hpointer).1; scalar_tac
        obtain ⟨newDepth, hnewDepth, hnewDepthVal⟩ := usize_sub_one_succeeds (hgeometry hpointer).1
        have hnewDepthNat : newDepth.val = fullDepth.val - 1 := by omega
        have hchildren (hdescend : ¬ RebaseHashShortcutFor origHash baseHash (rebaseLengths lengths)) :=
          rebaseChildren_success ValueInst origHash baseHash origLeft origRight baseLeft baseRight
            lengths fullDepth newDepth hnewDepth
            (by simpa only [rebaseLengths, Option.isSome_map, hnewDepthNat]
                using ((hgeometry hpointer).2 hdescend).1)
            (fun childLengths hselected => ih newDepth.val (by omega) origLeft baseLeft childLengths newDepth
              (Nat.le_refl _) (by
                rw [hselected, hnewDepthNat]
                exact ((hgeometry hpointer).2 hdescend).2.1) (by
                rw [hselected, hnewDepthNat]
                exact (hcompare hpointer (hgeometry hpointer).1 hdescend).1))
            (fun childLengths hselected => ih newDepth.val (by omega) origRight baseRight childLengths newDepth
              (Nat.le_refl _) (by
                rw [hselected, hnewDepthNat]
                exact ((hgeometry hpointer).2 hdescend).2.2) (by
                rw [hselected, hnewDepthNat]
                exact (hcompare hpointer (hgeometry hpointer).1 hdescend).2))
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
            | some pair =>
              obtain ⟨origLength, baseLength⟩ := pair
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
        | exact (hgeometry hpointer).elim

/-- Binary rebasing succeeds from only its reached geometry checks and
element calls. Whole-tree shapes, a global shift bound, packing layout, and
semantic content laws are unnecessary. -/
theorem Tree.rebase_on_success_of_geometry {T : Type} (ValueInst : Value T)
    (orig base : Tree T) (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize)
    (hgeometry : orig.RebaseGeometry base (rebaseLengths lengths) fullDepth.val)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val) :
    ∃ action, Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action) :=
  success_of_geometry_aux ValueInst fullDepth.val orig base lengths fullDepth (Nat.le_refl _) hgeometry hcompare

/-- The selected geometry and comparison laws are jointly necessary and
sufficient for success on arbitrary binary inputs and supplied metadata. -/
theorem Tree.rebase_on_success_iff_geometry {T : Type} (ValueInst : Value T)
    (orig base : Tree T) (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize) :
    (∃ action, Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) ↔
      orig.RebaseGeometry base (rebaseLengths lengths) fullDepth.val ∧
      orig.RebaseComparisons ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val := by
  constructor
  · rintro ⟨action, hrebase⟩
    exact ⟨Tree.rebase_on_geometry ValueInst hrebase, Tree.rebase_on_comparisons ValueInst hrebase⟩
  · rintro ⟨hgeometry, hcompare⟩
    exact Tree.rebase_on_success_of_geometry ValueInst orig base lengths fullDepth hgeometry hcompare

end milhouse.tree
