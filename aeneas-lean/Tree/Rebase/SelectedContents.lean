import Tree.Rebase.ContentInputs
import Tree.Rebase.GeometrySuccess

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem contents_of_inputs_aux {T : Type} (ValueInst : Value T) :
    ∀ (n : Nat) (orig base : Tree T) (lengths : Option (utils.Length × utils.Length))
      (fullDepth : Std.Usize) (action : RebaseAction (Tree T)),
      fullDepth.val ≤ n →
      orig.RebaseContentInputs ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val →
      Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action) →
      action.ContentsCorrect orig base := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro orig base lengths fullDepth action hmeasure hcontent hrebase
    unfold Tree.rebase_on at hrebase
    obtain ⟨pointerEqual, hpointer, hpointerTrue⟩ := triomphe.arc.Arc.ptr_eq_spec orig base
    rw [hpointer] at hrebase
    cases pointerEqual with
    | true =>
      simp at hrebase
      subst action
      have heq := hpointerTrue rfl
      simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, heq]
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases orig <;> cases base <;> simp only at hrebase
      case Leaf.Leaf origLeaf baseLeaf =>
        cases heq : triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq
            ValueInst.corecmpPartialEqInst origLeaf.value baseLeaf.value with
        | fail e => simp [heq] at hrebase
        | div => simp [heq] at hrebase
        | ok equal =>
          rw [heq] at hrebase
          cases equal with
          | false =>
            simp at hrebase
            subst action
            simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction]
          | true =>
            have helements := triomphe.arc.Arc.eq_true_imp_eq_on ValueInst.corecmpPartialEqInst
              (hcontent hpointer) heq
            simp at hrebase
            subst action
            simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction,
              Tree.elements, helements]
      case PackedLeaf.PackedLeaf origLeaf baseLeaf =>
        cases heq : milhouse_models.vec_eq ValueInst.corecmpPartialEqInst origLeaf.values baseLeaf.values with
        | fail e => simp [heq] at hrebase
        | div => simp [heq] at hrebase
        | ok equal =>
          rw [heq] at hrebase
          cases equal with
          | false =>
            simp at hrebase
            subst action
            simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction]
          | true =>
            have hvalues := (milhouse_models.vec_eq_sound_iff ValueInst.corecmpPartialEqInst
              origLeaf.values baseLeaf.values).mp (hcontent hpointer) heq
            simp at hrebase
            subst action
            simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, Tree.elements, hvalues]
      case Zero.Zero origDepth baseDepth =>
        simp [lift] at hrebase
        split at hrebase <;> simp at hrebase <;> subst action <;>
          simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, Tree.elements]
      case Node.Node origHash origLeft origRight baseHash baseLeft baseRight =>
        have childrenCorrect (hpositive : 0 < fullDepth.val)
            (hdescend : ¬ RebaseHashShortcutFor origHash baseHash (rebaseLengths lengths))
            (hchildren : rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
              lengths fullDepth = ok (.Ok action)) :
            action.ContentsCorrect (.Node origHash origLeft origRight) (.Node baseHash baseLeft baseRight) := by
          obtain ⟨newDepth, leftLengths, rightLengths, leftAction, rightAction,
            hdepthVal, _, hleftLengths, hrightLengths, hleft, hright, rfl⟩ :=
            rebaseChildren_selected_inputs ValueInst hchildren
          have hleftCorrect := ih newDepth.val (by omega) origLeft baseLeft leftLengths newDepth leftAction
            (Nat.le_refl _) (by
              rw [hleftLengths, hdepthVal]
              exact ((hcontent hpointer hpositive).2 hdescend).1) hleft
          have hrightCorrect := ih newDepth.val (by omega) origRight baseRight rightLengths newDepth rightAction
            (Nat.le_refl _) (by
              rw [hrightLengths, hdepthVal]
              exact ((hcontent hpointer hpositive).2 hdescend).2) hright
          exact combineRebaseActions_contents_correct origHash baseHash origLeft origRight baseLeft baseRight
            leftAction rightAction hleftCorrect hrightCorrect
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
            exact childrenCorrect hpositiveNat (fun hshortcut => hshortcut.1 hzero) hrebase
          · rename_i hnonzero
            split at hrebase
            · rename_i hhashEqual
              cases lengths with
              | none =>
                simp [core.option.Option.is_none_or] at hrebase
                subst action
                have helements := (hcontent hpointer hpositiveNat).1 ⟨hnonzero, hhashEqual, trivial⟩
                simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, Tree.elements, helements]
              | some pair =>
                obtain ⟨origLength, baseLength⟩ := pair
                simp! only [core.option.Option.is_none_or,
                  Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                  utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
                split at hrebase
                · rename_i hlength
                  simp at hrebase
                  subst action
                  have helements := (hcontent hpointer hpositiveNat).1
                    ⟨hnonzero, hhashEqual, congrArg UScalar.val hlength⟩
                  simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, Tree.elements, helements]
                · rename_i hlengthNe
                  exact childrenCorrect hpositiveNat
                    (fun hshortcut => hlengthNe (UScalar.eq_of_val_eq hshortcut.2.2)) hrebase
            · rename_i hhashNe
              exact childrenCorrect hpositiveNat (fun hshortcut => hhashNe hshortcut.2.1) hrebase
        · simp [hpositive] at hrebase
      all_goals simp at hrebase
      all_goals subst action
      all_goals simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction]

/-- Successful binary rebasing preserves materialized contents under only
soundness of the comparisons selected by its actual metadata. Equality actions
also certify agreement with the base. No layout, density, accurate lengths,
shape, capacity, comparison termination, or assumed child-success law is
required; absent lengths retain the actual unconditional length shortcut. -/
theorem Tree.rebase_on_contents_correct_of_inputs {T : Type} (ValueInst : Value T)
    {orig base : Tree T} {lengths : Option (utils.Length × utils.Length)}
    {fullDepth : Std.Usize} {action : RebaseAction (Tree T)}
    (hcontent : orig.RebaseContentInputs ValueInst.corecmpPartialEqInst base (rebaseLengths lengths) fullDepth.val)
    (hrebase : Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok action)) :
    action.ContentsCorrect orig base :=
  contents_of_inputs_aux ValueInst fullDepth.val orig base lengths fullDepth action (Nat.le_refl _) hcontent hrebase

end milhouse.tree
