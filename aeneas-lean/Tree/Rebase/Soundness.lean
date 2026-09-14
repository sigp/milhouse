import Tree.Rebase.PackedSoundness
import Tree.Arc.Equality

open Aeneas Aeneas.Std Result

namespace triomphe.arc.Arc

/-- Positive Arc comparison needs pointee soundness only for this pair, and
only when its pointers differ. The pointer shortcut supplies equality itself. -/
theorem eq_true_imp_eq_on {T : Type} (inst : core.cmp.PartialEq T T)
    {left right : T}
    (hsound : ptr_eq left right = ok false → inst.eq left right = ok true → left = right)
    (heq : Insts.CoreCmpPartialEqArc.eq inst left right = ok true) : left = right := by
  obtain ⟨same, hpointer, hsame⟩ := ptr_eq_spec left right
  cases same with
  | true => exact hsame rfl
  | false =>
    rw [eq_of_ptr_eq_false inst hpointer] at heq
    exact hsound hpointer heq

end triomphe.arc.Arc

namespace milhouse.tree

/-- Element soundness on corresponding leaves of these rebase inputs.
Pointer-equal trees or values and unequal-length packed vectors need no
element law. Packed pairs need soundness only when every paired `ne` returns
false; any other result omits all packed-pair obligations, including earlier
false answers. Pointer and hash shortcuts omit every descendant obligation.
The cache guard uses materialized lengths; the operational proof derives
agreement with the supplied Rust metadata from input density. -/
def Tree.RebaseEqualitySound {T : Type} (inst : core.cmp.PartialEq T T) : Tree T → Tree T → Prop
  | .Leaf left, .Leaf right =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.Leaf right : Tree T) = ok false →
      triomphe.arc.Arc.ptr_eq left.value right.value = ok false →
      inst.eq left.value right.value = ok true → left.value = right.value
  | .PackedLeaf left, .PackedLeaf right =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.PackedLeaf right : Tree T) = ok false →
      left.values.val.length = right.values.val.length →
      milhouse_models.NeSoundIfAllFalse inst (left.values.val.zip right.values.val)
  | .Node hash left right, .Node baseHash baseLeft baseRight =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false →
      (¬ RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
        (baseLeft.elements ++ baseRight.elements).length) →
      left.RebaseEqualitySound inst baseLeft ∧ right.RebaseEqualitySound inst baseRight
  | _, _ => True

/-- The packed branch's element law is exactly soundness of a positive vector
comparison when pointer identity has not already established equality. -/
theorem Tree.rebaseEqualitySound_packed_iff {T : Type} (inst : core.cmp.PartialEq T T)
    (left right : packed_leaf.PackedLeaf T) :
    (Tree.PackedLeaf left).RebaseEqualitySound inst (.PackedLeaf right) ↔
      (triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.PackedLeaf right : Tree T) = ok false →
        milhouse_models.vec_eq inst left.values right.values = ok true →
          left.values.val = right.values.val) := by
  constructor
  · intro hsound hpointer
    exact (milhouse_models.vec_eq_sound_iff inst left.values right.values).mp (hsound hpointer)
  · intro hsound hpointer
    exact (milhouse_models.vec_eq_sound_iff inst left.values right.values).mpr (hsound hpointer)

/-- Global soundness implies the weaker input-scoped law. No termination or
completeness of either comparison is needed. -/
theorem Tree.rebaseEqualitySound_of_sound {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ left right, inst.eq left right = ok true → left = right)
    (hne : ∀ left right, inst.ne left right = ok false → left = right)
    (orig base : Tree T) : orig.RebaseEqualitySound inst base := by
  induction orig generalizing base with
  | Leaf leaf =>
    cases base <;> simp only [Tree.RebaseEqualitySound]
    exact fun _ _ => heq _ _
  | PackedLeaf leaf =>
    cases base <;> simp only [Tree.RebaseEqualitySound]
    exact fun _ _ => milhouse_models.NeSoundIfAllFalse.of_neOn
      (milhouse_models.NeOn.of_all inst (milhouse_models.NeSoundAt inst) hne _)
  | Zero depth => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseEqualitySound]
    exact fun _ _ => ⟨ihleft _, ihright _⟩

end milhouse.tree
