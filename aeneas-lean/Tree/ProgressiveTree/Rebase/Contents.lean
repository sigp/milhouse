import Tree.ProgressiveTree.Rebase.Soundness
import Tree.ProgressiveTree.Rebase.Steps
import Tree.ProgressiveTree.Rebase.Geometry
import Tree.ProgressiveTree.Iter.Layer
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
  induction orig generalizing base after depth with
  | ProgressiveZero =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same => rfl
  | ProgressiveNode origHash origLeft origRight ih =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same => rfl
    | @node _ baseHash _ baseLeft _ baseRight newRight start capacity binary fullDepth origLeftLength baseLeftLength next
        action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright hpointer =>
      obtain ⟨hleftFit, hrightFit⟩ := hfit
      have horigLengthVal := ProgressiveTree.rebase_layer_length ValueInst hlayout hleftFit
        hstart hnext hcapacity hbinary horigLength
      have hbaseLengthVal := ProgressiveTree.rebase_layer_length ValueInst hlayout hleftFit
        hstart hnext hcapacity hbinary hbaseLength
      have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
      have hfullDepthVal := usize_add_val hfullDepth
      have horigLeft : DenseTree factor origLeft (2 * depth.val) origLeftLength.val := by
        simpa only [horigLengthVal] using horig.split_layer.1
      have hbaseLeft : DenseTree factor baseLeft (2 * depth.val) baseLeftLength.val := by
        simpa only [hbaseLengthVal] using hbase.split_layer.1
      have hnewLeft := tree.Tree.rebase_on_contents_correct ValueInst hlayout
        (by omega) horigLeft hbaseLeft (hequality hpointer).1 (hhashes hpointer).1 hleft
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      have hnextVal : next.val = depth.val + 1 := by omega
      have horigRight : origRight.Dense factor next.val (origLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using horig.right_remainder
      have hbaseRight : baseRight.Dense factor next.val (baseLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using hbase.right_remainder
      have hnewRight := ih horigRight hbaseRight
        (by simpa only [hnextVal] using hrightFit) (hequality hpointer).2 (hhashes hpointer).2 hright
      simp only [ProgressiveTree.elements]
      rw [hnewLeft.1, hnewRight]

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
