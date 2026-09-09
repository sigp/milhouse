import Tree.Rebase.Kind

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- The input-based classifier gives the exact category of every successful
Rust rebase action. Accurate dense metadata connects the stored contents to
the source's length guards. No element or cache soundness, comparison
termination, assumed child execution, or cache-validity premise is needed. -/
theorem Tree.rebase_on_kind_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
      ok (.Ok action)) :
    orig.rebaseKind ValueInst.corecmpPartialEqInst base = action.kind := by
  induction orig generalizing base depth origLength baseLength fullDepth action with
  | Leaf origLeaf | PackedLeaf origLeaf | Zero origDepth =>
    unfold Tree.rebase_on at hrebase
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec _ base
    rw [hpointer] at hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      exact Tree.rebaseKind_of_ptr_eq _ _ _ hpointer
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base <;> simp only at hrebase
      all_goals solve
        | (simp at hrebase <;> subst action <;>
            simp [Tree.rebaseKind, hpointer, RebaseAction.kind])
        | (rw [bind_eq_ok_iff] at hrebase
           obtain ⟨equal, hcompare, hrebase⟩ := hrebase
           cases equal <;> simp at hrebase <;> subst action <;>
             simp [Tree.rebaseKind, hpointer, hcompare, RebaseAction.kind])
        | (simp [lift] at hrebase
           split at hrebase <;> simp at hrebase <;> subst action <;>
             simp_all [Tree.rebaseKind, RebaseAction.kind])
  | Node origHash origLeft origRight ihleft ihright =>
    unfold Tree.rebase_on at hrebase
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec
      (.Node origHash origLeft origRight) base
    rw [hpointer] at hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      exact Tree.rebaseKind_of_ptr_eq _ _ _ hpointer
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base with
      | Leaf leaf => simp at hrebase
      | PackedLeaf leaf => simp at hrebase
      | Zero level =>
        simp at hrebase
        subst action
        simp [Tree.rebaseKind, hpointer, RebaseAction.kind]
      | Node baseHash baseLeft baseRight =>
        simp only at hrebase
        have childrenKind :
            (¬ RebaseHashShortcut origHash baseHash
              (origLeft.elements ++ origRight.elements).length
              (baseLeft.elements ++ baseRight.elements).length) →
            rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
              (some (origLength, baseLength)) fullDepth = ok (.Ok action) →
            (Tree.Node origHash origLeft origRight).rebaseKind ValueInst.corecmpPartialEqInst
              (.Node baseHash baseLeft baseRight) = action.kind := by
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
          have hleftKind := ihleft hnewFull
            (by simpa only [hlengths.1] using origLeftDense)
            (by simpa only [hlengths.2.1] using baseLeftDense) hleft
          have hrightKind := ihright hnewFull
            (by simpa only [hlengths.2.2.1] using origRightDense)
            (by simpa only [hlengths.2.2.2] using baseRightDense) hright
          rw [Tree.rebaseKind_of_descend _ _ _ _ _ _ _ hpointer hdescend,
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
              simp! only [core.option.Option.is_none_or,
                Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
              split at hrebase
              · rename_i hlength
                simp at hrebase
                subst action
                apply Tree.rebaseKind_of_hash_shortcut _ _ _ _ _ _ _ hpointer
                refine ⟨hnonzero, hhashEqual, ?_⟩
                change (Tree.Node origHash origLeft origRight).elements.length =
                  (Tree.Node baseHash baseLeft baseRight).elements.length
                rw [horig.elements_length, hbase.elements_length, hlength]
              · rename_i hlengthNe
                apply childrenKind ?_ hrebase
                intro hshortcut
                apply hlengthNe
                apply UScalar.eq_of_val_eq
                have hlength := hshortcut.2.2
                change (Tree.Node origHash origLeft origRight).elements.length =
                  (Tree.Node baseHash baseLeft baseRight).elements.length at hlength
                simpa only [horig.elements_length, hbase.elements_length] using hlength
            · rename_i hhashNe
              exact childrenKind (fun hshortcut => hhashNe hshortcut.2.1) hrebase
        · simp [hpositive] at hrebase

end milhouse.tree
