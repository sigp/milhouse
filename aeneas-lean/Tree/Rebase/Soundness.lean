import Tree.Rebase.ContentsAction
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

private theorem anyM_zip_ne_false_eq_on {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : _root_.List T) (hlength : orig.length = base.length)
    (hsound : ∀ pair ∈ orig.zip base, inst.ne pair.1 pair.2 = ok false → pair.1 = pair.2)
    (heq : _root_.List.anyM (fun pair => inst.ne pair.1 pair.2) (orig.zip base) = ok false) :
    orig = base := by
  induction orig generalizing base with
  | nil => cases base <;> simp_all
  | cons x xs ih =>
    cases base with
    | nil => simp at hlength
    | cons y ys =>
      simp only [_root_.List.length_cons, Nat.add_right_cancel_iff] at hlength
      simp only [_root_.List.zip_cons_cons, _root_.List.anyM_cons] at heq
      cases hxy : inst.ne x y with
      | fail e => simp [hxy] at heq
      | div => simp [hxy] at heq
      | ok different =>
        cases different with
        | true => simp [hxy, pure] at heq
        | false =>
          simp only [hxy, bind_tc_ok] at heq
          exact congrArg₂ _root_.List.cons (hsound (x, y) (by simp) hxy)
            (ih ys hlength (fun pair hpair => hsound pair (by simp [hpair])) heq)

/-- Positive vector comparison requires false-`ne` soundness only for paired
positions of these equal-length inputs. It needs no element `eq`, termination,
or law about unrelated values. Length agreement is derived from the call. -/
theorem vec_eq_contents_on {T : Type} (inst : core.cmp.PartialEq T T)
    {orig base : alloc.vec.Vec T}
    (hsound : orig.val.length = base.val.length →
      ∀ pair ∈ orig.val.zip base.val, inst.ne pair.1 pair.2 = ok false → pair.1 = pair.2)
    (heq : milhouse_models.vec_eq inst orig base = ok true) : orig.val = base.val := by
  unfold milhouse_models.vec_eq at heq
  cases hne : alloc.vec.partial_eq.PartialEqVec.ne inst orig base with
  | fail e => simp [hne] at heq
  | div => simp [hne] at heq
  | ok different =>
    cases different with
    | true => simp [hne] at heq
    | false =>
      unfold alloc.vec.partial_eq.PartialEqVec.ne at hne
      split at hne
      · exact anyM_zip_ne_false_eq_on inst orig.val base.val (by assumption)
          (hsound (by assumption)) hne
      · simp at hne

/-- Element soundness on corresponding leaves of these rebase inputs.
Pointer-equal trees or values and unequal-length packed vectors need no
element law. Binary children are included recursively, as in the existing
comparison-termination and cache-agreement scopes; this is not an exact trace
of calls selected after ancestor cache shortcuts. -/
def Tree.RebaseEqualitySound {T : Type} (inst : core.cmp.PartialEq T T) : Tree T → Tree T → Prop
  | .Leaf left, .Leaf right =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.Leaf right : Tree T) = ok false →
      triomphe.arc.Arc.ptr_eq left.value right.value = ok false →
      inst.eq left.value right.value = ok true → left.value = right.value
  | .PackedLeaf left, .PackedLeaf right =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.PackedLeaf right : Tree T) = ok false →
      left.values.val.length = right.values.val.length →
      ∀ pair ∈ left.values.val.zip right.values.val,
        inst.ne pair.1 pair.2 = ok false → pair.1 = pair.2
  | .Node hash left right, .Node baseHash baseLeft baseRight =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false →
      left.RebaseEqualitySound inst baseLeft ∧ right.RebaseEqualitySound inst baseRight
  | _, _ => True

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
    exact fun _ _ pair _ => hne pair.1 pair.2
  | Zero depth => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseEqualitySound]
    exact fun _ => ⟨ihleft _, ihright _⟩

end milhouse.tree
