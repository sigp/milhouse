import Tree.Rebase.SuccessReflection
import Tree.ProgressiveTree.Rebase.Success
import Tree.ProgressiveTree.Rebase.Steps

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- A progressive rebase that stops on a missing or shared input has no
element-comparison obligation in the omitted suffix. -/
theorem ProgressiveTree.rebaseComparisons_of_stop {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : ProgressiveTree T) (factor : Option Std.Usize)
    (packingDepth origLength baseLength depth : Nat)
    (hstop : orig = .ProgressiveZero ∨ base = .ProgressiveZero ∨
      triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseComparisons inst base factor packingDepth origLength baseLength depth := by
  rcases hstop with rfl | rfl | hpointer
  · cases base <;> trivial
  · cases orig <;> trivial
  · cases orig <;> cases base <;> simp only [ProgressiveTree.RebaseComparisons]
    intro hfalse
    rw [hpointer] at hfalse
    cases hfalse

/-- Successful progressive rebasing supplies its selected element-termination
law. Only layout and representability of the original layers connect the actual
capacity arithmetic to the scope; shape, density, comparison soundness, cache
validity, and input-length accuracy are unnecessary. Completed calls remain
available even when the final pointer checks reuse the original node. -/
theorem ProgressiveTree.rebase_on_recursive_comparisons {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hfit : orig.Fits factor depth.val)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (.Ok after)) :
    orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength.val baseLength.val depth.val := by
  induction orig generalizing base after depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode origHash origLeft origRight ih =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same _ _ hstop =>
      exact ProgressiveTree.rebaseComparisons_of_stop ValueInst.corecmpPartialEqInst _ _ _ _ _ _ _ hstop
    | @node _ baseHash _ baseLeft _ baseRight newRight start capacity binary fullDepth origLeftLength baseLeftLength next
        action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright hpointer =>
      have horigLengthVal := ProgressiveTree.rebase_layer_length ValueInst hlayout hfit.1
        hstart hnext hcapacity hbinary horigLength
      have hbaseLengthVal := ProgressiveTree.rebase_layer_length ValueInst hlayout hfit.1
        hstart hnext hcapacity hbinary hbaseLength
      have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
      have hfullDepthVal := usize_add_val hfullDepth
      have hfullDepthNat : fullDepth.val = 2 * depth.val + packingDepth.val := by omega
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      have hnextVal : next.val = depth.val + 1 := by omega
      refine fun _ => ⟨?_, ?_⟩
      · simpa only [rebaseLengths, Option.map_some, horigLengthVal, hbaseLengthVal, hfullDepthNat]
          using Tree.rebase_on_comparisons ValueInst hleft
      · have hrightCompare := ih (by simpa only [hnextVal] using hfit.2) hright
        simpa only [hnextVal] using hrightCompare

/-- Public progressive rebasing recovers the comparison scope at depth zero
from its successful execution, without a shape or semantic-content premise. -/
theorem ProgressiveTree.rebase_on_comparisons {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (hfit : orig.Fits factor 0)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) :
    orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength.val baseLength.val 0 :=
  ProgressiveTree.rebase_on_recursive_comparisons ValueInst hlayout hfit hrebase

/-- At compatible shapes and representable original layers, the selected
element comparisons are necessary and sufficient for recursive success. -/
theorem ProgressiveTree.rebase_on_recursive_success_iff {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32)
    (horig : orig.Shape factor depth.val) (hbase : base.Shape factor depth.val)
    (hfit : orig.Fits factor depth.val) :
    (∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (.Ok after)) ↔
      orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
        packingDepth.val origLength.val baseLength.val depth.val := by
  constructor
  · rintro ⟨after, hrebase⟩
    exact ProgressiveTree.rebase_on_recursive_comparisons ValueInst hlayout hfit hrebase
  · exact ProgressiveTree.rebase_on_recursive_success ValueInst hlayout
      orig base origLength baseLength depth horig hbase hfit

/-- The same exact success criterion applies to the public progressive call.
No comparison soundness, content equality, density, or cache law is required. -/
theorem ProgressiveTree.rebase_on_success_iff {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize)
    (horig : orig.Shape factor 0) (hbase : base.Shape factor 0)
    (hfit : orig.Fits factor 0) :
    (∃ after, ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) ↔
      orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
        packingDepth.val origLength.val baseLength.val 0 :=
  ProgressiveTree.rebase_on_recursive_success_iff ValueInst hlayout
    orig base origLength baseLength 0#u32 horig hbase hfit

end milhouse.progressive_tree
