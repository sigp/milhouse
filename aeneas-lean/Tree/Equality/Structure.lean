import Tree.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Equality of tree structure and materialized values, ignoring every hash
    cache. In particular, zero depths and leaf variants still distinguish
    trees that happen to have the same materialized sequence. -/
def Tree.StructuralEq {T : Type} : Tree T → Tree T → Prop
  | .Leaf left, .Leaf right => left.value = right.value
  | .PackedLeaf left, .PackedLeaf right => left.values.val = right.values.val
  | .Node _ left right, .Node _ otherLeft otherRight =>
      left.StructuralEq otherLeft ∧ right.StructuralEq otherRight
  | .Zero left, .Zero right => left = right
  | _, _ => False

theorem Tree.StructuralEq.refl {T : Type} (self : Tree T) : self.StructuralEq self := by
  induction self <;> simp_all [Tree.StructuralEq]

/-- Structural equality implies exact sequence agreement without density,
    packing, hash, or scalar-bound assumptions. -/
theorem Tree.StructuralEq.elements_eq {T : Type} {self other : Tree T}
    (heq : self.StructuralEq other) : self.elements = other.elements := by
  induction self generalizing other <;> cases other <;>
    simp_all [Tree.StructuralEq, Tree.elements]
  case Node.Node hash left right ihLeft ihRight otherHash otherLeft otherRight =>
    rw [ihLeft heq.1, ihRight heq.2]

/-- Structural equality transports the full binary density invariant. -/
theorem Tree.StructuralEq.dense {T : Type} {self other : Tree T}
    {factor : Option Std.Usize} {depth length : Nat}
    (heq : self.StructuralEq other) (hdense : DenseTree factor self depth length) :
    DenseTree factor other depth length := by
  induction hdense generalizing other with
  | zero factor depth =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    subst heq
    exact .zero factor depth
  | leaf value =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    exact .leaf _
  | packed factor value hnonempty hfit =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    simpa only [heq] using DenseTree.packed factor _ (by simpa only [heq] using hnonempty)
      (by simpa only [heq] using hfit)
  | node factor hash left right child leftLength rightLength hleft hright hnonempty hfull ihLeft ihRight =>
    cases other <;> simp only [Tree.StructuralEq] at heq
    exact .node factor _ _ _ child leftLength rightLength (ihLeft heq.1) (ihRight heq.2) hnonempty hfull

end milhouse.tree
