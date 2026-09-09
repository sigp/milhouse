import Tree.Equality.Inputs
import Tree.Equality.Structure

open Aeneas Aeneas.Std Result

namespace milhouse.tree

/-- Element laws for derived tree equality on these inputs. Shared children
need no law, a right child needs one only after structural agreement on the
left, and packed vectors follow the actual short-circuit element calls.
The correctness proofs establish left agreement before using the right law. -/
def Tree.EqualityOn {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop) :
    Tree T → Tree T → Prop
  | .Leaf left, .Leaf right =>
      triomphe.arc.Arc.ptr_eq left.value right.value = ok false → P left.value right.value
  | .PackedLeaf left, .PackedLeaf right =>
      left.values.val.length = right.values.val.length →
      milhouse_models.NeOn inst P (left.values.val.zip right.values.val)
  | .Node _ left right, .Node _ otherLeft otherRight =>
      (triomphe.arc.Arc.ptr_eq left otherLeft = ok false → left.EqualityOn inst P otherLeft) ∧
      (left.StructuralEq otherLeft → triomphe.arc.Arc.ptr_eq right otherRight = ok false →
        right.EqualityOn inst P otherRight)
  | _, _ => True

/-- Concrete Arc equality additionally skips the entire tree on pointer
identity. Plain derived equality itself has no outer pointer shortcut. -/
def Tree.ArcEqualityOn {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (self other : Tree T) : Prop :=
  triomphe.arc.Arc.ptr_eq self other = ok false → self.EqualityOn inst P other

theorem Tree.equalityOn_of_all {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (hpairs : ∀ left right, P left right) (self other : Tree T) : self.EqualityOn inst P other := by
  induction self generalizing other with
  | Leaf leaf => cases other <;> simp only [Tree.EqualityOn]; exact fun _ => hpairs _ _
  | PackedLeaf leaf =>
    cases other <;> simp only [Tree.EqualityOn]
    exact fun _ => milhouse_models.NeOn.of_all inst P hpairs _
  | Zero depth => cases other <;> trivial
  | Node hash left right ihleft ihright =>
    cases other <;> simp only [Tree.EqualityOn]
    exact ⟨fun _ => ihleft _, fun _ _ => ihright _⟩

theorem Tree.arcEqualityOn_of_all {T : Type} (inst : core.cmp.PartialEq T T) (P : T → T → Prop)
    (hpairs : ∀ left right, P left right) (self other : Tree T) : self.ArcEqualityOn inst P other :=
  fun _ => self.equalityOn_of_all inst P hpairs other

theorem Tree.EqualityOn.mono {T : Type} {inst : core.cmp.PartialEq T T} {P Q : T → T → Prop}
    (himp : ∀ left right, P left right → Q left right)
    {self other : Tree T} (hscope : self.EqualityOn inst P other) : self.EqualityOn inst Q other := by
  induction self generalizing other with
  | Leaf leaf =>
    cases other <;> simp only [Tree.EqualityOn]
    exact fun hpointer => himp _ _ (hscope hpointer)
  | PackedLeaf leaf =>
    cases other <;> simp only [Tree.EqualityOn]
    exact fun hlength => (hscope hlength).mono himp
  | Zero depth => cases other <;> trivial
  | Node hash left right ihleft ihright =>
    cases other <;> simp only [Tree.EqualityOn]
    exact ⟨fun hpointer => ihleft (hscope.1 hpointer),
      fun hleft hpointer => ihright (hscope.2 hleft hpointer)⟩

theorem Tree.ArcEqualityOn.mono {T : Type} {inst : core.cmp.PartialEq T T} {P Q : T → T → Prop}
    (himp : ∀ left right, P left right → Q left right)
    {self other : Tree T} (hscope : self.ArcEqualityOn inst P other) : self.ArcEqualityOn inst Q other :=
  fun hpointer => (hscope hpointer).mono himp

end milhouse.tree
