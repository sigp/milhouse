import Tree.Rebase.SelectedKindReflection
import Tree.Rebase.SelectedCacheInputs
import Tree.Rebase.SelectedContents
import Tree.Rebase.CacheAction

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- At arbitrary supplied metadata and cache-subject depth, selected input
cache laws are necessary and sufficient for a successful binary result's
cache invariant. Only the selected content soundness law is assumed; layout,
density, shape, capacity, accurate lengths, and query success are unnecessary. -/
theorem Tree.rebase_on_cache_iff_of_inputs {T : Type} (ValueInst : Value T)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base : Tree T} {lengths : Option (utils.Length × utils.Length)}
    {fullDepth : Std.Usize} {depth : Nat} {action : RebaseAction (Tree T)}
    (hcontent : orig.RebaseContentInputs ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val)
    (hrebase : Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) :
    (applyRebaseAction orig action).CachesOn P depth ↔
      orig.RebaseCacheInputs ValueInst.corecmpPartialEqInst P base (rebaseLengths lengths) fullDepth.val depth := by
  induction orig generalizing base lengths fullDepth depth action with
  | Leaf origLeaf | PackedLeaf origLeaf | Zero origDepth =>
    have hkind := Tree.rebase_on_kindFor_spec ValueInst hrebase
    unfold Tree.rebase_on at hrebase
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec _ base
    rw [hpointer] at hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction]
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base <;> simp only at hrebase
      all_goals solve
        | (simp at hrebase <;> subst action <;>
            simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction])
        | (rw [bind_eq_ok_iff] at hrebase
           obtain ⟨equal, hcompare, hrebase⟩ := hrebase
           cases equal <;> simp at hrebase <;> subst action <;>
             simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction])
  | Node origHash origLeft origRight ihleft ihright =>
    have hkind := Tree.rebase_on_kindFor_spec ValueInst hrebase
    unfold Tree.rebase_on at hrebase
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec
      (.Node origHash origLeft origRight) base
    rw [hpointer] at hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction]
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base with
      | Leaf leaf => simp at hrebase
      | PackedLeaf leaf => simp at hrebase
      | Zero level =>
        simp at hrebase
        subst action
        simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction]
      | Node baseHash baseLeft baseRight =>
        simp only at hrebase
        have childrenCaches :
            0 < fullDepth.val →
            (¬ RebaseHashShortcutFor origHash baseHash (rebaseLengths lengths)) →
            rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
              lengths fullDepth = ok (.Ok action) →
            ((applyRebaseAction (.Node origHash origLeft origRight) action).CachesOn P depth ↔
              (Tree.Node origHash origLeft origRight).RebaseCacheInputs ValueInst.corecmpPartialEqInst P
                (.Node baseHash baseLeft baseRight) (rebaseLengths lengths) fullDepth.val depth) := by
          intro hpositive hdescend hchildren
          obtain ⟨newDepth, leftLengths, rightLengths, leftAction, rightAction,
            hdepthVal, _, hleftLengths, hrightLengths, hleft, hright, rfl⟩ :=
            rebaseChildren_selected_inputs ValueInst hchildren
          have hleftContent : origLeft.RebaseContentInputs ValueInst.corecmpPartialEqInst baseLeft
              (rebaseLengths leftLengths) newDepth.val := by
            rw [hleftLengths, hdepthVal]
            exact ((hcontent hpointer hpositive).2 hdescend).1
          have hrightContent : origRight.RebaseContentInputs ValueInst.corecmpPartialEqInst baseRight
              (rebaseLengths rightLengths) newDepth.val := by
            rw [hrightLengths, hdepthVal]
            exact ((hcontent hpointer hpositive).2 hdescend).2
          have hleftIff := ihleft (depth := depth - 1) hleftContent hleft
          have hrightIff := ihright (depth := depth - 1) hrightContent hright
          rw [hleftLengths, hdepthVal] at hleftIff
          rw [hrightLengths, hdepthVal] at hrightIff
          have hleftContents := Tree.rebase_on_contents_correct_of_inputs ValueInst hleftContent hleft
          have hrightContents := Tree.rebase_on_contents_correct_of_inputs ValueInst hrightContent hright
          have hcombined := combineRebaseActions_cache_iff P origHash baseHash origLeft origRight baseLeft baseRight
            leftAction rightAction depth (fun _ => hleftContents.1) (fun _ => hrightContents.1)
          rw [← combineRebaseActions_kind origHash baseHash origLeft origRight baseLeft baseRight
            leftAction rightAction] at hcombined
          rw [Tree.RebaseCacheInputs.eq_def, hkind]
          cases haction : combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
              leftAction rightAction with
          | NotEqualNoop | EqualNoop =>
            simp only [RebaseAction.kind, applyRebaseAction]
          | EqualReplace replacement =>
            simpa [haction, RebaseAction.kind] using hcombined
          | NotEqualReplace replacement =>
            simp only [RebaseAction.kind]
            refine Iff.trans ?_ (and_congr Iff.rfl (and_congr hleftIff hrightIff))
            simpa [haction, RebaseAction.kind] using hcombined
        by_cases hpositive : fullDepth > 0#usize
        · have hpositiveNat : 0 < fullDepth.val := by scalar_tac
          rw [if_pos hpositive] at hrebase
          simp [lock_api.rwlock.RwLock.read,
            lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
            alloy_primitives.bits.fixed.FixedBytes.is_zero,
            alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
            triomphe.arc.Arc.new] at hrebase
          split at hrebase
          · rename_i hzero
            exact childrenCaches hpositiveNat (fun hshortcut => hshortcut.1 hzero) hrebase
          · rename_i hnonzero
            split at hrebase
            · rename_i hhashEqual
              cases lengths with
              | none =>
                simp [core.option.Option.is_none_or] at hrebase
                subst action
                simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction]
              | some pair =>
                obtain ⟨origLength, baseLength⟩ := pair
                simp! only [core.option.Option.is_none_or,
                  Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                  utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
                split at hrebase
                · rename_i hlength
                  simp at hrebase
                  subst action
                  simp only [Tree.RebaseCacheInputs.eq_def, hkind, RebaseAction.kind, applyRebaseAction]
                · rename_i hlengthNe
                  exact childrenCaches hpositiveNat (fun hshortcut => hlengthNe (UScalar.eq_of_val_eq hshortcut.2.2)) hrebase
            · rename_i hhashNe
              exact childrenCaches hpositiveNat (fun hshortcut => hhashNe hshortcut.2.1) hrebase
        · simp [hpositive] at hrebase

end milhouse.tree
