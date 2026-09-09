import Tree.Equality.Scope
import Tree.ProgressiveTree.Equality.Structure

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_tree

/-- Element laws for compared progressive layers. Suffix laws are required
only after binary-layer agreement, and pointer sharing skips whole subtrees. -/
def ProgressiveTree.EqualityOn {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop) :
    ProgressiveTree T → ProgressiveTree T → Prop
  | .ProgressiveNode _ left right, .ProgressiveNode _ otherLeft otherRight =>
      left.ArcEqualityOn inst P otherLeft ∧
      (left.StructuralEq otherLeft → triomphe.arc.Arc.ptr_eq right otherRight = ok false →
        right.EqualityOn inst P otherRight)
  | _, _ => True

def ProgressiveTree.ArcEqualityOn {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (self other : ProgressiveTree T) : Prop :=
  triomphe.arc.Arc.ptr_eq self other = ok false → self.EqualityOn inst P other

theorem ProgressiveTree.equalityOn_of_all {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (hpairs : ∀ left right, P left right) (self other : ProgressiveTree T) :
    self.EqualityOn inst P other := by
  induction self generalizing other with
  | ProgressiveZero => cases other <;> trivial
  | ProgressiveNode hash left right ih =>
    cases other <;> simp only [ProgressiveTree.EqualityOn]
    exact ⟨left.arcEqualityOn_of_all inst P hpairs _, fun _ _ => ih _⟩

theorem ProgressiveTree.arcEqualityOn_of_all {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (hpairs : ∀ left right, P left right) (self other : ProgressiveTree T) :
    self.ArcEqualityOn inst P other := fun _ => self.equalityOn_of_all inst P hpairs other

theorem ProgressiveTree.EqualityOn.mono {T : Type} {inst : core.cmp.PartialEq T T} {P Q : T → T → Prop}
    (himp : ∀ left right, P left right → Q left right)
    {self other : ProgressiveTree T} (hscope : self.EqualityOn inst P other) :
    self.EqualityOn inst Q other := by
  induction self generalizing other with
  | ProgressiveZero => cases other <;> trivial
  | ProgressiveNode hash left right ih =>
    cases other <;> simp only [ProgressiveTree.EqualityOn]
    exact ⟨hscope.1.mono himp, fun hleft hpointer => ih (hscope.2 hleft hpointer)⟩

theorem ProgressiveTree.ArcEqualityOn.mono {T : Type} {inst : core.cmp.PartialEq T T} {P Q : T → T → Prop}
    (himp : ∀ left right, P left right → Q left right)
    {self other : ProgressiveTree T} (hscope : self.ArcEqualityOn inst P other) :
    self.ArcEqualityOn inst Q other := fun hpointer => (hscope hpointer).mono himp

end milhouse.progressive_tree
