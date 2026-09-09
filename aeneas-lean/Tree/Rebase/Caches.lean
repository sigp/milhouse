import Tree.Rebase.CacheAction
import Tree.Rebase.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Successful binary rebasing preserves contents and every cache predicate
indexed by logical input and depth. The semantic comparison laws establish unchanged
child contents before an original parent cache is reused. No hash computation,
cache write, or assumed intermediate successful call is needed. -/
theorem Tree.rebase_on_cache_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (horigCache : orig.CachesOn P depth) (hbaseCache : base.CachesOn P depth)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
      ok (core.result.Result.Ok action)) :
    action.ContentsCorrect orig base ∧ (applyRebaseAction orig action).CachesOn P depth := by
  refine ⟨Tree.rebase_on_contents_correct ValueInst hlayout
    hdepth horig hbase hequality hhashes hrebase, ?_⟩
  induction orig generalizing base depth origLength baseLength fullDepth action with
  | Node origHash origLeft origRight ihleft ihright =>
    unfold Tree.rebase_on at hrebase
    obtain ⟨pointerEqual, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec
      (.Node origHash origLeft origRight) base
    rw [hpointer] at hrebase
    cases pointerEqual with
    | true =>
      simp at hrebase
      subst action
      exact horigCache
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base with
      | Leaf leaf => simp at hrebase
      | PackedLeaf leaf => simp at hrebase
      | Zero zeroDepth =>
        simp at hrebase
        subst action
        exact horigCache
      | Node baseHash baseLeft baseRight =>
        simp only at hrebase
        have childrenCorrect :
            (¬ RebaseHashShortcut origHash baseHash
              (origLeft.elements ++ origRight.elements).length
              (baseLeft.elements ++ baseRight.elements).length) →
            rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
            (some (origLength, baseLength)) fullDepth = ok (core.result.Result.Ok action) →
            (applyRebaseAction (.Node origHash origLeft origRight) action).CachesOn P depth := by
          intro hdescend hchildren
          obtain ⟨newDepth, mapped, leftLengths, rightLengths, leftAction, rightAction,
            hnewDepth, hmapped, hsplit, hleft, hright, rfl⟩ := rebaseChildren_success_state ValueInst hchildren
          have hnewDepthVal := usize_sub_one_val hnewDepth
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
          have hol : DenseTree factor origLeft child ol.val := by
            simpa only [hlengths.1] using origLeftDense
          have hbl : DenseTree factor baseLeft child bl.val := by
            simpa only [hlengths.2.1] using baseLeftDense
          have hor : DenseTree factor origRight child or.val := by
            simpa only [hlengths.2.2.1] using origRightDense
          have hbr : DenseTree factor baseRight child br.val := by
            simpa only [hlengths.2.2.2] using baseRightDense
          simp only [Tree.CachesOn, Nat.add_sub_cancel] at horigCache hbaseCache
          have hleftContents := Tree.rebase_on_contents_correct ValueInst hlayout
            hnewFull hol hbl (hequality hpointer hdescend).1 ((hhashes hpointer).2 hdescend).1 hleft
          have hrightContents := Tree.rebase_on_contents_correct ValueInst hlayout
            hnewFull hor hbr (hequality hpointer hdescend).2 ((hhashes hpointer).2 hdescend).2 hright
          exact combineRebaseActions_preserves_caches P origHash baseHash origLeft origRight
            baseLeft baseRight leftAction rightAction child horigCache.1 hbaseCache
            hleftContents.1 hrightContents.1
            (ihleft hnewFull hol hbl (hequality hpointer hdescend).1 ((hhashes hpointer).2 hdescend).1 horigCache.2.1 hbaseCache.2.1 hleft)
            (ihright hnewFull hor hbr (hequality hpointer hdescend).2 ((hhashes hpointer).2 hdescend).2 horigCache.2.2 hbaseCache.2.2 hright)
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
            exact childrenCorrect (fun hshortcut => hshortcut.1 hzero) hrebase
          · split at hrebase
            · simp! only [core.option.Option.is_none_or,
                Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
              split at hrebase
              · simp at hrebase
                subst action
                exact hbaseCache
              · rename_i hlengthNe
                apply childrenCorrect ?_ hrebase
                intro hshortcut
                apply hlengthNe
                apply UScalar.eq_of_val_eq
                have hlength := hshortcut.2.2
                change (Tree.Node origHash origLeft origRight).elements.length =
                  (Tree.Node baseHash baseLeft baseRight).elements.length at hlength
                simpa only [horig.elements_length, hbase.elements_length] using hlength
            · rename_i hhashNe
              exact childrenCorrect (fun hshortcut => hhashNe hshortcut.2.1) hrebase
        · simp [hpositive] at hrebase
  | Leaf origLeaf | PackedLeaf origLeaf | Zero origDepth =>
    unfold Tree.rebase_on at hrebase
    obtain ⟨pointerEqual, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec _ base
    rw [hpointer] at hrebase
    cases pointerEqual with
    | true =>
      simp at hrebase
      subst action
      exact horigCache
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base <;> simp only at hrebase
      all_goals first
        | (simp at hrebase <;> subst action <;> exact horigCache)
        | (rw [bind_eq_ok_iff] at hrebase
           obtain ⟨equal, _, hrebase⟩ := hrebase
           cases equal <;> simp at hrebase <;> subst action
           · exact horigCache
           · exact hbaseCache)

end milhouse.tree
