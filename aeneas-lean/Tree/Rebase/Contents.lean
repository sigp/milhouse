import Tree.Rebase.Soundness
import Tree.Arc.Equality

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private theorem rebase_contents_aux {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) :
    ∀ (n : Nat) (orig base : Tree T) (depth : Nat) (origLength baseLength fullDepth : Std.Usize)
      (action : RebaseAction (Tree T)),
      fullDepth.val ≤ n → fullDepth.val = depth + packingDepth.val →
      DenseTree factor orig depth origLength.val → DenseTree factor base depth baseLength.val →
      orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base →
      orig.CachedHashesAgree base →
      Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
        ok (core.result.Result.Ok action) → action.ContentsCorrect orig base := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro orig base depth origLength baseLength fullDepth action hmeasure hdepth horig hbase hequality hhashes hrebase
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
              (hequality hpointer) heq
            simp at hrebase
            subst action
            simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction,
              Tree.elements, helements]
      case PackedLeaf.PackedLeaf origLeaf baseLeaf =>
        cases heq : milhouse_models.vec_eq ValueInst.corecmpPartialEqInst
            origLeaf.values baseLeaf.values with
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
            have hvalues := vec_eq_contents_on ValueInst.corecmpPartialEqInst (hequality hpointer) heq
            simp at hrebase
            subst action
            simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, Tree.elements, hvalues]
      case Zero.Zero origDepth baseDepth =>
        simp [lift] at hrebase
        split at hrebase <;> simp at hrebase <;> subst action <;>
          simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction, Tree.elements]
      case Node.Node origHash origLeft origRight baseHash baseLeft baseRight =>
        have childrenCorrect : rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
            (some (origLength, baseLength)) fullDepth = ok (core.result.Result.Ok action) →
            action.ContentsCorrect (.Node origHash origLeft origRight) (.Node baseHash baseLeft baseRight) := by
          intro hchildren
          obtain ⟨newDepth, mapped, leftLengths, rightLengths, leftAction, rightAction,
            hnewDepth, hmapped, hsplit, hleft, hright, rfl⟩ := rebaseChildren_success_state ValueInst hchildren
          have hnewDepthVal := usize_sub_one_val hnewDepth
          have hsmall : newDepth.val < n := by omega
          simp only [core.option.Option.map] at hmapped
          rw [bind_eq_ok_iff] at hmapped
          obtain ⟨⟨⟨ol, bl⟩, or, br⟩, hlengthSplit, hmapped⟩ := hmapped
          simp only [ok.injEq] at hmapped
          subst mapped
          simp only [core.option.OptionPair.unzip, ok.injEq, Prod.mk.injEq] at hsplit
          obtain ⟨rfl, rfl⟩ := hsplit
          have hlengths := rebase_split_lengths_spec ValueInst hlengthSplit
          obtain ⟨child, hchild⟩ : ∃ child, depth = child + 1 := by
            have hshape := horig.shape
            cases hshape with
            | @node _ _ _ child _ _ _ => exact ⟨child, rfl⟩
          subst depth
          have hnewFull : newDepth.val = child + packingDepth.val := by omega
          have hcapacity : 2 ^ newDepth.val = subtreeCapacity factor child := by
            rw [hlayout.subtreeCapacity_eq_two_pow, hnewFull, Nat.add_comm child packingDepth.val]
          rw [hcapacity] at hlengths
          obtain ⟨origLeftDense, origRightDense⟩ := horig.split_node
          obtain ⟨baseLeftDense, baseRightDense⟩ := hbase.split_node
          have hleftCorrect := ih newDepth.val hsmall origLeft baseLeft child ol bl newDepth leftAction
            (Nat.le_refl _) hnewFull (by simpa only [hlengths.1] using origLeftDense)
            (by simpa only [hlengths.2.1] using baseLeftDense) hequality.1 hhashes.2.1 hleft
          have hrightCorrect := ih newDepth.val hsmall origRight baseRight child or br newDepth rightAction
            (Nat.le_refl _) hnewFull (by simpa only [hlengths.2.2.1] using origRightDense)
            (by simpa only [hlengths.2.2.2] using baseRightDense) hequality.2 hhashes.2.2 hright
          exact combineRebaseActions_contents_correct origHash baseHash origLeft origRight baseLeft baseRight
            leftAction rightAction hleftCorrect hrightCorrect
        by_cases hpositive : fullDepth > 0#usize
        · rw [if_pos hpositive] at hrebase
          simp [lock_api.rwlock.RwLock.read,
            lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
            alloy_primitives.bits.fixed.FixedBytes.is_zero,
            alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
            triomphe.arc.Arc.new] at hrebase
          split at hrebase
          · exact childrenCorrect hrebase
          · rename_i hnonzero
            split at hrebase
            · rename_i hhashEqual
              simp! only [core.option.Option.is_none_or,
                Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
              split at hrebase
              · rename_i hlength
                simp at hrebase
                subst action
                have hlengths : (origLeft.elements ++ origRight.elements).length =
                    (baseLeft.elements ++ baseRight.elements).length := by
                  change (Tree.Node origHash origLeft origRight).elements.length =
                    (Tree.Node baseHash baseLeft baseRight).elements.length
                  rw [horig.elements_length, hbase.elements_length, hlength]
                have helements := hhashes.1 hnonzero hhashEqual hlengths
                simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction,
                  Tree.elements, helements]
              · exact childrenCorrect hrebase
            · exact childrenCorrect hrebase
        · simp [hpositive] at hrebase
      all_goals simp at hrebase
      all_goals subst action
      all_goals simp [RebaseAction.ContentsCorrect, RebaseAction.IsEqual, applyRebaseAction]

/-- Successful rebasing preserves the original materialized sequence, and
    equality actions also certify agreement with the base. Length and depth
    metadata describe the dense inputs. Positive element `eq` and false element
    `ne` identify equal values, covering unpacked and packed comparisons
    respectively; corresponding caches agree at equal materialized lengths. -/
theorem Tree.rebase_on_contents_correct {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
      ok (core.result.Result.Ok action)) : action.ContentsCorrect orig base := by
  exact rebase_contents_aux ValueInst hlayout fullDepth.val orig base depth origLength baseLength fullDepth action
    (Nat.le_refl _) hdepth horig hbase hequality hhashes hrebase

end milhouse.tree
