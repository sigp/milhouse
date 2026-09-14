import Tree.ProgressiveTree.Rebase.Ready

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Compatible shapes and representable original layers guarantee successful
rebasing when the compared leaves terminate. All layer arithmetic is derived;
the base needs no capacity bound, and recorded lengths need not match contents. -/
theorem ProgressiveTree.rebase_on_recursive_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32)
    (horig : orig.Shape factor depth.val) (hbase : base.Shape factor depth.val)
    (hfit : orig.Fits factor depth.val)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength.val baseLength.val depth.val) :
    ∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (.Ok after) :=
  ProgressiveTree.rebase_on_recursive_success_of_ready ValueInst orig base origLength baseLength depth
    (Or.inr ⟨factor, packingDepth, RebasePackingQueries.of_layout hlayout,
      ProgressiveTree.rebaseRequirements_of_invariants ValueInst hlayout horig hbase hfit hcompare⟩)

/-- Public progressive rebasing succeeds from shape and original capacity
invariants, without density, clone, or cached-hash assumptions. -/
theorem ProgressiveTree.rebase_on_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize)
    (horig : orig.Shape factor 0) (hbase : base.Shape factor 0)
    (hfit : orig.Fits factor 0)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength.val baseLength.val 0) :
    ∃ after, ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after) :=
  ProgressiveTree.rebase_on_recursive_success ValueInst hlayout orig base origLength baseLength 0#u32
    horig hbase hfit hcompare

end milhouse.progressive_tree
