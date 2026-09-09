import Tree.Shape
import Tree.Arc.Equality

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

/-- Vector comparison terminates when the element `ne` calls at paired
positions do. Different-length vectors require no element-comparison law. -/
theorem vec_eq_success {T U : Type} (inst : core.cmp.PartialEq T U)
    (left : alloc.vec.Vec T) (right : alloc.vec.Vec U)
    (hne : left.val.length = right.val.length →
      ∀ pair ∈ left.val.zip right.val, ∃ different, inst.ne pair.1 pair.2 = ok different) :
    ∃ equal, vec_eq inst left right = ok equal := by
  have hloop : ∀ pairs : _root_.List (T × U),
      (∀ pair ∈ pairs, ∃ different, inst.ne pair.1 pair.2 = ok different) →
      ∃ different, _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) pairs = ok different := by
    intro pairs
    induction pairs with
    | nil => intro _; exact ⟨false, rfl⟩
    | cons pair pairs ih =>
      intro hne
      obtain ⟨different, hcompare⟩ := hne pair (by simp)
      cases different with
      | true => exact ⟨true, by simp [_root_.List.anyM_cons, hcompare, pure]⟩
      | false =>
        obtain ⟨different, htail⟩ := ih (fun item hitem => hne item (by simp [hitem]))
        exact ⟨different, by simp [_root_.List.anyM_cons, hcompare, htail]⟩
  unfold vec_eq alloc.vec.partial_eq.PartialEqVec.ne
  split
  · obtain ⟨different, hcompare⟩ := hloop _ (hne (by assumption))
    exact ⟨!different, by simp [hcompare]⟩
  · exact ⟨false, rfl⟩

end milhouse_models

namespace milhouse.tree

/-- Termination laws for potentially compared leaf pairs. They are scoped to
corresponding positions of these input trees, not arbitrary values of T.
Pointer-equal leaves and unequal-length packed vectors need no element law. -/
def Tree.RebaseComparisons {T : Type} (inst : core.cmp.PartialEq T T) : Tree T → Tree T → Prop
  | .Leaf left, .Leaf right =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.Leaf right : Tree T) = ok false →
      triomphe.arc.Arc.ptr_eq left.value right.value = ok false →
      ∃ equal, inst.eq left.value right.value = ok equal
  | .PackedLeaf left, .PackedLeaf right =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.PackedLeaf right : Tree T) = ok false →
      left.values.val.length = right.values.val.length →
      ∀ pair ∈ left.values.val.zip right.values.val,
        ∃ different, inst.ne pair.1 pair.2 = ok different
  | .Node _ left right, .Node _ baseLeft baseRight =>
      left.RebaseComparisons inst baseLeft ∧ right.RebaseComparisons inst baseRight
  | _, _ => True

/-- Ordinary totality laws for an element type imply the scoped pair law.
The operation specifications can instead use the weaker scoped condition. -/
theorem Tree.rebaseComparisons_of_total {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ left right, ∃ equal, inst.eq left right = ok equal)
    (hne : ∀ left right, ∃ different, inst.ne left right = ok different)
    (orig base : Tree T) : orig.RebaseComparisons inst base := by
  induction orig generalizing base with
  | Leaf value =>
    cases base <;> simp only [Tree.RebaseComparisons]
    exact fun _ _ => heq _ _
  | PackedLeaf value =>
    cases base <;> simp only [Tree.RebaseComparisons]
    exact fun _ _ pair _ => hne pair.1 pair.2
  | Zero depth => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseComparisons]
    exact ⟨ihleft _, ihright _⟩

end milhouse.tree
