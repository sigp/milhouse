import Tree.ProgressiveTree.Rebase.Steps
import Tree.ProgressiveTree.Rebase.Geometry
import Tree.ProgressiveTree.Iter.Layer
import Tree.Rebase.Lengths

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Recursive progressive rebasing preserves the original dense suffix and
    its capacity bounds. The base needs accurate dense lengths, but no capacity
    invariant: only levels present in the original tree are visited. -/
theorem ProgressiveTree.rebase_on_recursive_preserves_backing {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (horig : orig.Dense factor depth.val (origLength.val - progressiveCapacity factor depth.val))
    (hbase : base.Dense factor depth.val (baseLength.val - progressiveCapacity factor depth.val))
    (hfit : orig.Fits factor depth.val)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (core.result.Result.Ok after)) :
    after.Dense factor depth.val (origLength.val - progressiveCapacity factor depth.val) ∧
      after.Fits factor depth.val := by
  induction orig generalizing base after depth with
  | ProgressiveZero =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same => exact ⟨horig, hfit⟩
  | ProgressiveNode origHash origLeft origRight ih =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same => exact ⟨horig, hfit⟩
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
      have hnewLeft := tree.Tree.rebase_on_preserves_dense_length ValueInst hlayout
        (by omega) horigLeft hbaseLeft hleft
      rw [horigLengthVal] at hnewLeft
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      have hnextVal : next.val = depth.val + 1 := by omega
      have horigRight : origRight.Dense factor next.val (origLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using horig.right_remainder
      have hbaseRight : baseRight.Dense factor next.val (baseLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using hbase.right_remainder
      obtain ⟨hnewRight, hnewRightFit⟩ := ih horigRight hbaseRight
        (by simpa only [hnextVal] using hrightFit) hright
      have hremaining : origLength.val - progressiveCapacity factor next.val =
          (origLength.val - progressiveCapacity factor depth.val) - subtreeCapacity factor (2 * depth.val) := by
        rw [hnextVal, progressiveCapacity_succ, Nat.sub_sub]
      have hsum : origLength.val - progressiveCapacity factor depth.val =
          min (origLength.val - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val)) +
            (origLength.val - progressiveCapacity factor next.val) := by omega
      refine ⟨?_, hleftFit, by simpa only [hnextVal] using hnewRightFit⟩
      rw [hsum]
      exact .node origHash hnewLeft (by simpa only [hnextVal] using hnewRight) (by omega)

/-- Public progressive rebasing preserves the complete backing invariant for
    its original length, including rebasing onto shorter or longer trees. -/
theorem ProgressiveTree.rebase_on_preserves_backing {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (horig : orig.Dense factor 0 origLength.val) (hbase : base.Dense factor 0 baseLength.val)
    (hfit : orig.Fits factor 0)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength =
      ok (core.result.Result.Ok after)) :
    after.Dense factor 0 origLength.val ∧ after.Fits factor 0 := by
  have horig' : orig.Dense factor (0#u32).val (origLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using horig
  have hbase' : base.Dense factor (0#u32).val (baseLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using hbase
  have hresult := ProgressiveTree.rebase_on_recursive_preserves_backing ValueInst hlayout
    horig' hbase' hfit hrebase
  simpa [progressiveCapacity] using hresult

end milhouse.progressive_tree
