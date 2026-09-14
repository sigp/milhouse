import Tree.Rebase.Comparisons

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- The four operational action categories, without their replacement trees.
`notEqual` categories do not assert semantic inequality of the inputs. -/
inductive RebaseKind where
  | notEqualNoop
  | notEqualReplace
  | equalNoop
  | equalReplace
  deriving DecidableEq

def RebaseAction.kind {A : Type} : RebaseAction A → RebaseKind
  | .NotEqualNoop => .notEqualNoop
  | .NotEqualReplace _ => .notEqualReplace
  | .EqualNoop => .equalNoop
  | .EqualReplace _ => .equalReplace

/-- The source combiner's categories, including its ordered mixed-equality
cases: a no-op left child with a replaced right child rebuilds the original
parent; a replaced equal left child and equal right child import the base. -/
def RebaseKind.combine : RebaseKind → RebaseKind → RebaseKind
  | .equalReplace, .equalNoop | .equalReplace, .equalReplace => .equalReplace
  | .equalNoop, .equalNoop => .equalNoop
  | .notEqualNoop, .notEqualNoop | .notEqualNoop, .equalNoop
  | .equalNoop, .notEqualNoop => .notEqualNoop
  | _, _ => .notEqualReplace

/-- Erasing replacement payloads commutes with the actual action combiner. -/
theorem combineRebaseActions_kind {T : Type}
    (origHash baseHash : CacheHash) (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T)) :
    (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
      leftAction rightAction).kind = leftAction.kind.combine rightAction.kind := by
  cases leftAction <;> cases rightAction <;> rfl

/-- Input-based category of successful rebasing at accurate dense lengths.
This records actual pointer, element, and cache decisions, without assuming
comparison soundness or a result tree. Failed or diverging element calls are
assigned a no-op category; the reflection theorem only uses successful runs. -/
noncomputable def Tree.rebaseKind {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : Tree T) : RebaseKind := by
  classical
  exact if triomphe.arc.Arc.ptr_eq orig base = ok false then
    match orig, base with
    | .Leaf left, .Leaf right =>
        if triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq inst left.value right.value = ok true
        then .equalReplace else .notEqualNoop
    | .PackedLeaf left, .PackedLeaf right =>
        if milhouse_models.vec_eq inst left.values right.values = ok true
        then .equalReplace else .notEqualNoop
    | .Zero left, .Zero right => if left = right then .equalReplace else .notEqualNoop
    | .Node hash left right, .Node baseHash baseLeft baseRight =>
        if RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
            (baseLeft.elements ++ baseRight.elements).length then .equalReplace
        else (left.rebaseKind inst baseLeft).combine (right.rebaseKind inst baseRight)
    | _, _ => .notEqualNoop
  else .equalNoop

/-- Pointer sharing has the no-op category without inspecting descendants. -/
theorem Tree.rebaseKind_of_ptr_eq {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : Tree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.rebaseKind inst base = .equalNoop := by
  rw [Tree.rebaseKind.eq_def]
  simp [hpointer]

/-- A hash shortcut selects whole-base replacement without element laws. -/
theorem Tree.rebaseKind_of_hash_shortcut {T : Type} (inst : core.cmp.PartialEq T T)
    (hash baseHash : CacheHash) (left right baseLeft baseRight : Tree T)
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hshortcut : RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
      (baseLeft.elements ++ baseRight.elements).length) :
    (Tree.Node hash left right).rebaseKind inst (.Node baseHash baseLeft baseRight) = .equalReplace := by
  rw [Tree.rebaseKind]
  simp only [hpointer, ↓reduceIte, if_pos hshortcut]

/-- When neither outer shortcut is taken, the category is determined by the
two child categories in the source's exact combination order. -/
theorem Tree.rebaseKind_of_descend {T : Type} (inst : core.cmp.PartialEq T T)
    (hash baseHash : CacheHash) (left right baseLeft baseRight : Tree T)
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hdescend : ¬ RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
      (baseLeft.elements ++ baseRight.elements).length) :
    (Tree.Node hash left right).rebaseKind inst (.Node baseHash baseLeft baseRight) =
      (left.rebaseKind inst baseLeft).combine (right.rebaseKind inst baseRight) := by
  rw [Tree.rebaseKind]
  simp only [hpointer, ↓reduceIte, if_neg hdescend]

end milhouse.tree
