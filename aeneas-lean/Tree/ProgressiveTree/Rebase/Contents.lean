import Tree.ProgressiveTree.Rebase.SelectedContents
import Tree.Rebase.Contents

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Recursive rebasing preserves the exact materialized suffix under sound
    positive element `eq`, false element `ne`, and agreement of the compared
    binary caches. -/
theorem ProgressiveTree.rebase_on_recursive_preserves_contents {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (horig : orig.Dense factor depth.val (origLength.val - progressiveCapacity factor depth.val))
    (hbase : base.Dense factor depth.val (baseLength.val - progressiveCapacity factor depth.val))
    (hfit : orig.Fits factor depth.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (core.result.Result.Ok after)) :
    after.elements = orig.elements := by
  exact ProgressiveTree.rebase_on_recursive_preserves_contents_of_inputs ValueInst
    (ProgressiveTree.rebaseContentInputs_of_dense ValueInst hlayout
      (origLength := origLength.val) (baseLength := baseLength.val)
      horig hbase hfit hequality hhashes) hrebase

/-- Public progressive rebasing preserves the materialized sequence even for
    shorter or longer bases, under the semantic laws for equality and caches. -/
theorem ProgressiveTree.rebase_on_preserves_contents {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (horig : orig.Dense factor 0 origLength.val) (hbase : base.Dense factor 0 baseLength.val)
    (hfit : orig.Fits factor 0)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength =
      ok (core.result.Result.Ok after)) :
    after.elements = orig.elements := by
  have horig' : orig.Dense factor (0#u32).val (origLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using horig
  have hbase' : base.Dense factor (0#u32).val (baseLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using hbase
  exact ProgressiveTree.rebase_on_recursive_preserves_contents ValueInst hlayout
    horig' hbase' hfit hequality hhashes hrebase

end milhouse.progressive_tree
