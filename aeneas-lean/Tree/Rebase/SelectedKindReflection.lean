import Tree.Rebase.SelectedKind
import Tree.Rebase.GeometrySuccess

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- The supplied-metadata classifier gives the exact category of every
successful binary rebase. Its actual pointer result is recovered without
invoking the pointer contract. No layout, geometry, accurate-length, semantic
comparison/hash, comparison-termination, or assumed child-success law is used. -/
theorem Tree.rebase_on_kindFor_spec {T : Type} (ValueInst : Value T)
    {orig base : Tree T} {lengths : Option (utils.Length × utils.Length)}
    {fullDepth : Std.Usize} {action : RebaseAction (Tree T)}
    (hrebase : Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) :
    orig.rebaseKindFor ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val = action.kind := by
  induction orig generalizing base lengths fullDepth action with
  | Leaf origLeaf | PackedLeaf origLeaf | Zero origDepth =>
    unfold Tree.rebase_on at hrebase
    rw [bind_eq_ok_iff] at hrebase
    obtain ⟨same, hpointer, hrebase⟩ := hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      exact Tree.rebaseKindFor_of_ptr_eq _ _ _ _ _ hpointer
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base <;> simp only at hrebase
      all_goals solve
        | (simp at hrebase <;> subst action <;>
            simp [Tree.rebaseKindFor, hpointer, RebaseAction.kind])
        | (rw [bind_eq_ok_iff] at hrebase
           obtain ⟨equal, hcompare, hrebase⟩ := hrebase
           cases equal <;> simp at hrebase <;> subst action <;>
             simp [Tree.rebaseKindFor, hpointer, hcompare, RebaseAction.kind])
        | (simp [lift] at hrebase
           split at hrebase <;> simp at hrebase <;> subst action <;>
             simp_all [Tree.rebaseKindFor, RebaseAction.kind])
  | Node origHash origLeft origRight ihleft ihright =>
    unfold Tree.rebase_on at hrebase
    rw [bind_eq_ok_iff] at hrebase
    obtain ⟨same, hpointer, hrebase⟩ := hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      exact Tree.rebaseKindFor_of_ptr_eq _ _ _ _ _ hpointer
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base with
      | Leaf leaf => simp at hrebase
      | PackedLeaf leaf => simp at hrebase
      | Zero level =>
        simp at hrebase
        subst action
        simp [Tree.rebaseKindFor, hpointer, RebaseAction.kind]
      | Node baseHash baseLeft baseRight =>
        simp only at hrebase
        have childrenKind :
            (¬ RebaseHashShortcutFor origHash baseHash (rebaseLengths lengths)) →
            rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
              lengths fullDepth = ok (.Ok action) →
            (Tree.Node origHash origLeft origRight).rebaseKindFor ValueInst.corecmpPartialEqInst
              (.Node baseHash baseLeft baseRight) (rebaseLengths lengths) fullDepth.val = action.kind := by
          intro hdescend hchildren
          obtain ⟨newDepth, leftLengths, rightLengths, leftAction, rightAction,
            hdepthVal, _, hleftLengths, hrightLengths, hleft, hright, rfl⟩ :=
            rebaseChildren_selected_inputs ValueInst hchildren
          have hleftKind := ihleft hleft
          have hrightKind := ihright hright
          rw [hleftLengths, hdepthVal] at hleftKind
          rw [hrightLengths, hdepthVal] at hrightKind
          rw [Tree.rebaseKindFor_of_descend _ _ _ _ _ _ _ _ _ hpointer hdescend,
            hleftKind, hrightKind, combineRebaseActions_kind]
        by_cases hpositive : fullDepth > 0#usize
        · rw [if_pos hpositive] at hrebase
          simp [lock_api.rwlock.RwLock.read,
            lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
            alloy_primitives.bits.fixed.FixedBytes.is_zero,
            alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
            triomphe.arc.Arc.new] at hrebase
          split at hrebase
          · rename_i hzero
            exact childrenKind (fun hshortcut => hshortcut.1 hzero) hrebase
          · rename_i hnonzero
            split at hrebase
            · rename_i hhashEqual
              cases lengths with
              | none =>
                simp [core.option.Option.is_none_or] at hrebase
                subst action
                exact Tree.rebaseKindFor_of_hash_shortcut _ _ _ _ _ _ _ _ _ hpointer
                  ⟨hnonzero, hhashEqual, trivial⟩
              | some pair =>
                obtain ⟨origLength, baseLength⟩ := pair
                simp! only [core.option.Option.is_none_or,
                  Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                  utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
                split at hrebase
                · rename_i hlength
                  simp at hrebase
                  subst action
                  exact Tree.rebaseKindFor_of_hash_shortcut _ _ _ _ _ _ _ _ _ hpointer
                    ⟨hnonzero, hhashEqual, congrArg UScalar.val hlength⟩
                · rename_i hlengthNe
                  exact childrenKind (fun hshortcut => hlengthNe (UScalar.eq_of_val_eq hshortcut.2.2)) hrebase
            · rename_i hhashNe
              exact childrenKind (fun hshortcut => hhashNe hshortcut.2.1) hrebase
        · simp [hpositive] at hrebase

end milhouse.tree
