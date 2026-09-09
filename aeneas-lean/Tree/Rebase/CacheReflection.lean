import Tree.Rebase.Caches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Every valid successful result supplies both selected input-cache laws.
The semantic comparison laws identify retained caches' logical subjects;
no original/base cache validity or assumed child result is a premise. -/
theorem Tree.rebase_on_cache_inputs {T : Type} (ValueInst : Value T)
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
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth = ok (.Ok action))
    (hcache : (applyRebaseAction orig action).CachesOn P depth) :
    orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth ∧
      orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth := by
  induction orig generalizing base depth origLength baseLength fullDepth action with
  | Node origHash origLeft origRight ihleft ihright =>
    have hkind := Tree.rebase_on_kind_spec ValueInst hlayout hdepth horig hbase hrebase
    unfold Tree.rebase_on at hrebase
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec (.Node origHash origLeft origRight) base
    rw [hpointer] at hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def]
      simpa only [hkind, RebaseAction.kind, and_true, applyRebaseAction] using hcache
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base with
      | Leaf leaf => simp at hrebase
      | PackedLeaf leaf => simp at hrebase
      | Zero level =>
        simp at hrebase
        subst action
        rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def]
        simpa only [hkind, RebaseAction.kind, and_true, applyRebaseAction] using hcache
      | Node baseHash baseLeft baseRight =>
        simp only at hrebase
        have childrenInputs :
            (¬ RebaseHashShortcut origHash baseHash
              (origLeft.elements ++ origRight.elements).length
              (baseLeft.elements ++ baseRight.elements).length) →
            rebaseChildren ValueInst origHash baseHash origLeft origRight baseLeft baseRight
              (some (origLength, baseLength)) fullDepth = ok (.Ok action) →
            (Tree.Node origHash origLeft origRight).RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P
                (.Node baseHash baseLeft baseRight) depth ∧
              (Tree.Node origHash origLeft origRight).RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P
                (.Node baseHash baseLeft baseRight) depth := by
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
          have hleftContents := Tree.rebase_on_contents_correct ValueInst hlayout
            hnewFull hol hbl (hequality hpointer hdescend).1 ((hhashes hpointer).2 hdescend).1 hleft
          have hrightContents := Tree.rebase_on_contents_correct ValueInst hlayout
            hnewFull hor hbr (hequality hpointer hdescend).2 ((hhashes hpointer).2 hdescend).2 hright
          have hinputs := combineRebaseActions_cache_inputs P origHash baseHash origLeft origRight
            baseLeft baseRight leftAction rightAction child (fun _ => hleftContents.1)
            (fun _ => hrightContents.1) hcache
          rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def]
          cases haction : combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
              leftAction rightAction with
          | NotEqualNoop | EqualNoop =>
            simpa only [hkind, haction, RebaseAction.kind, applyRebaseAction, and_true] using hcache
          | EqualReplace replacement =>
            have hreplace : leftAction.kind.combine rightAction.kind = .equalReplace := by
              rw [← combineRebaseActions_kind origHash baseHash origLeft origRight baseLeft baseRight, haction]
              rfl
            simpa only [hkind, haction, RebaseAction.kind, true_and] using hinputs.1 hreplace
          | NotEqualReplace replacement =>
            have hkeep : leftAction.kind.combine rightAction.kind ≠ .equalReplace := by
              rw [← combineRebaseActions_kind origHash baseHash origLeft origRight baseLeft baseRight, haction]
              simp [RebaseAction.kind]
            obtain ⟨hroot, hleftCache, hrightCache⟩ := hinputs.2 hkeep
            obtain ⟨hleftOrig, hleftBase⟩ := ihleft hnewFull hol hbl
              (hequality hpointer hdescend).1 ((hhashes hpointer).2 hdescend).1 hleft hleftCache
            obtain ⟨hrightOrig, hrightBase⟩ := ihright hnewFull hor hbr
              (hequality hpointer hdescend).2 ((hhashes hpointer).2 hdescend).2 hright hrightCache
            simpa only [hkind, haction, RebaseAction.kind, Nat.add_sub_cancel] using
              And.intro (And.intro hroot (And.intro hleftOrig hrightOrig)) (And.intro hleftBase hrightBase)
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
            exact childrenInputs (fun hshortcut => hshortcut.1 hzero) hrebase
          · split at hrebase
            · simp! only [core.option.Option.is_none_or,
                Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
                utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq] at hrebase
              split at hrebase
              · simp at hrebase
                subst action
                rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def]
                simpa only [hkind, RebaseAction.kind, true_and, applyRebaseAction] using hcache
              · rename_i hlengthNe
                apply childrenInputs ?_ hrebase
                intro hshortcut
                apply hlengthNe
                apply UScalar.eq_of_val_eq
                have hlength := hshortcut.2.2
                change (Tree.Node origHash origLeft origRight).elements.length =
                  (Tree.Node baseHash baseLeft baseRight).elements.length at hlength
                simpa only [horig.elements_length, hbase.elements_length] using hlength
            · rename_i hhashNe
              exact childrenInputs (fun hshortcut => hhashNe hshortcut.2.1) hrebase
        · simp [hpositive] at hrebase
  | Leaf origLeaf | PackedLeaf origLeaf | Zero origDepth =>
    have hkind := Tree.rebase_on_kind_spec ValueInst hlayout hdepth horig hbase hrebase
    unfold Tree.rebase_on at hrebase
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec _ base
    rw [hpointer] at hrebase
    cases same with
    | true =>
      simp at hrebase
      subst action
      rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def]
      simpa only [hkind, RebaseAction.kind, and_true, applyRebaseAction] using hcache
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref] at hrebase
      cases base <;> simp only at hrebase
      all_goals solve
        | (simp at hrebase <;> subst action <;>
            rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def] <;>
            simpa only [hkind, RebaseAction.kind, and_true, true_and, applyRebaseAction] using hcache)
        | (rw [bind_eq_ok_iff] at hrebase
           obtain ⟨equal, _, hrebase⟩ := hrebase
           cases equal <;> simp at hrebase <;> subst action <;>
             rw [Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def] <;>
             simpa only [hkind, RebaseAction.kind, and_true, true_and, applyRebaseAction] using hcache)

/-- Under the semantic content laws and accurate dense metadata, the two
selected input-cache laws are jointly necessary and sufficient for cache
validity after successful rebasing. No cache premise is assumed by this iff. -/
theorem Tree.rebase_on_cache_iff {T : Type} (ValueInst : Value T)
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
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth = ok (.Ok action)) :
    (applyRebaseAction orig action).CachesOn P depth ↔
      orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth ∧
        orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth := by
  constructor
  · exact Tree.rebase_on_cache_inputs ValueInst hlayout P hdepth horig hbase hequality hhashes hrebase
  · rintro ⟨horigCache, hbaseCache⟩
    exact (Tree.rebase_on_cache_spec ValueInst hlayout P hdepth horig hbase
      hequality hhashes horigCache hbaseCache hrebase).2

end milhouse.tree
