import Tree.Rebase.Steps
import Tree.Rebase.HashShortcut

open Aeneas Aeneas.Std Result

namespace milhouse.tree

/-- Supplied rebase lengths, retaining `none` as the unconditional
length-agreement branch used by vectors. These are metadata, not contents. -/
abbrev RebaseLengths := Option (Nat × Nat)

def rebaseLengths (lengths : Option (utils.Length × utils.Length)) : RebaseLengths :=
  lengths.map (fun pair => (pair.1.val, pair.2.val))

def rebaseLeftLengths (lengths : RebaseLengths) (childDepth : Nat) : RebaseLengths :=
  lengths.map (fun pair => (min pair.1 (2 ^ childDepth), min pair.2 (2 ^ childDepth)))

def rebaseRightLengths (lengths : RebaseLengths) (childDepth : Nat) : RebaseLengths :=
  lengths.map (fun pair => (pair.1 - 2 ^ childDepth, pair.2 - 2 ^ childDepth))

/-- The shortcut decision uses the supplied optional lengths even when those
lengths do not describe the stored values. It assumes no hash correctness. -/
def RebaseHashShortcutFor (origHash baseHash : CacheHash) (lengths : RebaseLengths) : Prop :=
  (¬ ∀ byte ∈ origHash.val, byte = 0#u8) ∧ origHash.val = baseHash.val ∧
    lengths.elim True (fun pair => pair.1 = pair.2)

/-- The actual successful length split supplies exactly the next comparison
scope's metadata. No subtree-density or input-length consistency is needed. -/
theorem rebase_split_comparison_inputs {T : Type} (ValueInst : Value T)
    {origLength baseLength newDepth origLeft baseLeft origRight baseRight : Std.Usize}
    (hsplit : Tree.rebase_on.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairLengthLengthPairPairLengthLengthPairLengthLength.call_once
      ValueInst newDepth (origLength, baseLength) = ok ((origLeft, baseLeft), (origRight, baseRight))) :
    rebaseLengths (some (origLeft, baseLeft)) =
        rebaseLeftLengths (rebaseLengths (some (origLength, baseLength))) newDepth.val ∧
      rebaseLengths (some (origRight, baseRight)) =
        rebaseRightLengths (rebaseLengths (some (origLength, baseLength))) newDepth.val := by
  obtain ⟨hol, hbl, hor, hbr⟩ := rebase_split_lengths_spec ValueInst hsplit
  simp [rebaseLengths, rebaseLeftLengths, rebaseRightLengths, hol, hbl, hor, hbr]

end milhouse.tree
