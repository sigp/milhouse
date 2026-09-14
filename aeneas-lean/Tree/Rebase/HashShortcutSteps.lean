import Tree.Rebase.HashShortcut

open Aeneas Aeneas.Std Result

namespace milhouse.tree

/-- A selected cache shortcut immediately succeeds and returns the base.
Only the actual branch guards are needed: no child shape, element comparison,
hash validity, collision, or recursive-success premise is required to obtain
this operational result. Collision soundness is a separate content obligation. -/
theorem Tree.rebase_on_of_hash_shortcut {T : Type} (ValueInst : Value T)
    (origHash baseHash : CacheHash) (origLeft origRight baseLeft baseRight : Tree T)
    (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize)
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node origHash origLeft origRight : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hpositive : fullDepth > 0#usize)
    (hnonzero : ¬ ∀ byte ∈ origHash.val, byte = 0#u8)
    (hhash : origHash.val = baseHash.val)
    (hlengths : ∀ pair ∈ lengths, pair.1 = pair.2) :
    Tree.rebase_on ValueInst (.Node origHash origLeft origRight)
      (.Node baseHash baseLeft baseRight) lengths fullDepth =
      ok (.Ok (.EqualReplace (.Node baseHash baseLeft baseRight))) := by
  rw [Tree.rebase_on, hpointer]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, if_pos hpositive,
    lock_api.rwlock.RwLock.read,
    lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
    alloy_primitives.bits.fixed.FixedBytes.is_zero,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq,
    List.all_eq_true, beq_iff_eq, decide_eq_true_eq, if_neg hnonzero, if_pos hhash]
  cases lengths with
  | none => rfl
  | some pair =>
    obtain ⟨origLength, baseLength⟩ := pair
    have hequal : origLength = baseLength := hlengths (origLength, baseLength) (by simp)
    simp! only [core.option.Option.is_none_or,
      Tree.rebase_on.closure.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthBool.call_once,
      utils.Length.Insts.CoreCmpPartialEqLength.eq, bind_tc_ok, decide_eq_true_eq]
    simp [hequal]

end milhouse.tree
