import Tree.Rebase.ContentInputs
import Tree.ProgressiveTree.Rebase.Soundness
import Tree.ProgressiveTree.Rebase.Requirements
import Tree.ProgressiveTree.Rebase.PackingQueries
import Tree.ProgressiveTree.Iter.Layer

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Content laws for the actual binary inputs at each entered progressive
layer. Successful packing queries select the clamped lengths and full depth;
no query success, coherence, shape, density, or capacity law is assumed here.
Missing/shared suffixes impose no semantic obligation. -/
def ProgressiveTree.RebaseContentInputs {T : Type} (ValueInst : Value T) :
    ProgressiveTree T → ProgressiveTree T → Nat → Nat → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight,
      origLength, baseLength, depth =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      ∀ factor packingDepth, RebasePackingQueries ValueInst.tree_hashTreeHashInst factor packingDepth →
      left.RebaseContentInputs ValueInst.corecmpPartialEqInst baseLeft
        (some (rebaseLayerLength factor origLength depth, rebaseLayerLength factor baseLength depth))
        (2 * depth + packingDepth.val) ∧
      right.RebaseContentInputs ValueInst baseRight origLength baseLength (depth + 1)
  | _, _, _, _, _ => True

/-- For valid dense inputs, the previous semantic laws imply the actual
metadata-specific content scope. Packing-query uniqueness identifies the
layout's metadata; representability is used only by this adapter to remove
the machine clamps, not by the general operational content theorem. -/
theorem ProgressiveTree.rebaseContentInputs_of_dense {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : ProgressiveTree T} {origLength baseLength depth : Nat}
    (horig : orig.Dense factor depth (origLength - progressiveCapacity factor depth))
    (hbase : base.Dense factor depth (baseLength - progressiveCapacity factor depth))
    (hfit : orig.Fits factor depth)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base) :
    orig.RebaseContentInputs ValueInst base origLength baseLength depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      intro hpointer actualFactor actualDepth hqueries
      obtain ⟨rfl, rfl⟩ := hqueries.unique (RebasePackingQueries.of_layout hlayout)
      constructor
      · rw [rebaseLayerLength_of_fits hlayout origLength depth hfit.1,
          rebaseLayerLength_of_fits hlayout baseLength depth hfit.1]
        exact tree.Tree.rebaseContentInputs_of_dense ValueInst hlayout rfl
          horig.split_layer.1 hbase.split_layer.1 (hequality hpointer).1 (hhashes hpointer).1
      · exact ih horig.right_remainder hbase.right_remainder hfit.2 (hequality hpointer).2 (hhashes hpointer).2

end milhouse.progressive_tree
