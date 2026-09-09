import Tree.Rebase.ComparisonInputs
import Tree.Arc.Equality
import Tree.Rebase.ElementComparisons

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse_models

/-- Arc comparison needs an element call only when pointer identity fails. -/
theorem arc_eq_success {T : Type} (inst : core.cmp.PartialEq T T) (left right : T)
    (heq : triomphe.arc.Arc.ptr_eq left right = ok false →
      ∃ equal, inst.eq left right = ok equal) :
    ∃ equal, triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq inst left right = ok equal := by
  obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec left right
  cases same with
  | true => exact ⟨true, triomphe.arc.Arc.eq_of_ptr_eq_true inst hpointer⟩
  | false =>
    obtain ⟨equal, hcompare⟩ := heq hpointer
    exact ⟨equal, (triomphe.arc.Arc.eq_of_ptr_eq_false inst hpointer).trans hcompare⟩

/-- Vector comparison terminates when the element calls actually reached by
its `ne` loop do. Unequal-length vectors require no element call; equal-length
vectors stop at the first true `ne` without laws on subsequent pairs. -/
theorem vec_eq_success {T U : Type} (inst : core.cmp.PartialEq T U)
    (left : alloc.vec.Vec T) (right : alloc.vec.Vec U)
    (hne : left.val.length = right.val.length → NeComparisons inst (left.val.zip right.val)) :
    ∃ equal, vec_eq inst left right = ok equal := by
  unfold vec_eq alloc.vec.partial_eq.PartialEqVec.ne
  split
  · obtain ⟨different, hcompare⟩ := (hne (by assumption)).anyM_success
    exact ⟨!different, by simp [hcompare]⟩
  · exact ⟨false, rfl⟩

end milhouse_models

namespace milhouse.tree

/-- Termination laws for the leaf pairs reached using the supplied lengths
and full depth. Pointer and cache shortcuts omit all descendants. The scope
uses no materialized-length or density assumption; `none` allows the cache
shortcut regardless of either tree's stored contents. -/
def Tree.RebaseComparisons {T : Type} (inst : core.cmp.PartialEq T T) :
    Tree T → Tree T → RebaseLengths → Nat → Prop
  | .Leaf left, .Leaf right, _, _ =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.Leaf right : Tree T) = ok false →
      triomphe.arc.Arc.ptr_eq left.value right.value = ok false →
      ∃ equal, inst.eq left.value right.value = ok equal
  | .PackedLeaf left, .PackedLeaf right, _, _ =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.PackedLeaf right : Tree T) = ok false →
      left.values.val.length = right.values.val.length →
      milhouse_models.NeComparisons inst (left.values.val.zip right.values.val)
  | .Node hash left right, .Node baseHash baseLeft baseRight, lengths, fullDepth =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false →
      0 < fullDepth → ¬ RebaseHashShortcutFor hash baseHash lengths →
      left.RebaseComparisons inst baseLeft (rebaseLeftLengths lengths (fullDepth - 1)) (fullDepth - 1) ∧
        right.RebaseComparisons inst baseRight (rebaseRightLengths lengths (fullDepth - 1)) (fullDepth - 1)
  | _, _, _, _ => True

/-- Ordinary totality laws imply the scope at arbitrary supplied lengths and
full depth. The operation specifications use only the weaker selected law. -/
theorem Tree.rebaseComparisons_of_total {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ left right, ∃ equal, inst.eq left right = ok equal)
    (hne : ∀ left right, ∃ different, inst.ne left right = ok different)
    (orig base : Tree T) (lengths : RebaseLengths) (fullDepth : Nat) :
    orig.RebaseComparisons inst base lengths fullDepth := by
  induction orig generalizing base lengths fullDepth with
  | Leaf value =>
    cases base <;> simp only [Tree.RebaseComparisons]
    exact fun _ _ => heq _ _
  | PackedLeaf value =>
    cases base <;> simp only [Tree.RebaseComparisons]
    exact fun _ _ => milhouse_models.neComparisons_of_pairs inst _ (fun pair _ => hne pair.1 pair.2)
  | Zero depth => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseComparisons]
    exact fun _ _ _ => ⟨ihleft _ _ _, ihright _ _ _⟩

/-- A selected hash shortcut needs no terminating element comparison, even
when all comparisons in its descendants fail or diverge. -/
theorem Tree.rebaseComparisons_of_hash_shortcut {T : Type} (inst : core.cmp.PartialEq T T)
    (hash baseHash : CacheHash) (left right baseLeft baseRight : Tree T)
    (lengths : RebaseLengths) (fullDepth : Nat)
    (hshortcut : RebaseHashShortcutFor hash baseHash lengths) :
    (Tree.Node hash left right).RebaseComparisons inst (.Node baseHash baseLeft baseRight)
      lengths fullDepth := by
  intro _ _ hdescend
  exact (hdescend hshortcut).elim

end milhouse.tree
