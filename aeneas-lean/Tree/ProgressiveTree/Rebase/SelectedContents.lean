import Tree.Rebase.SelectedContents
import Tree.ProgressiveTree.Rebase.ContentInputs
import Tree.ProgressiveTree.Rebase.Ready

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Actual progressive rebasing preserves its materialized suffix under only
the selected content laws. Packing queries, clamped lengths, and completed
child calls are recovered from execution. No layout, density, shape, capacity,
accurate-length, comparison-termination, or query-success premise is needed. -/
theorem ProgressiveTree.rebase_on_recursive_preserves_contents_of_inputs {T : Type} (ValueInst : Value T)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hcontent : orig.RebaseContentInputs ValueInst base origLength.val baseLength.val depth.val)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after)) :
    after.elements = orig.elements := by
  induction orig generalizing base after depth with
  | ProgressiveZero =>
    rw [ProgressiveTree.rebase_on_recursive_stop_state ValueInst (Or.inl rfl) hrebase]
  | ProgressiveNode origHash origLeft origRight ih =>
    rcases ProgressiveTree.rebase_on_recursive_ready ValueInst hrebase with hstop | ⟨factor, packingDepth, hqueries, _⟩
    · rw [ProgressiveTree.rebase_on_recursive_stop_state ValueInst hstop hrebase]
    · cases ProgressiveTree.rebase_on_recursive_step_of_depth_query ValueInst hqueries.depth_eq hrebase with
      | same => rfl
      | @node _ baseHash _ baseLeft _ baseRight newRight start capacity binary fullDepth origLeftLength baseLeftLength next
          action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright hpointer =>
        obtain ⟨hleftContent, hrightContent⟩ := hcontent hpointer factor packingDepth hqueries
        have horigLengthVal := ProgressiveTree.rebase_layer_length_clamped ValueInst hqueries.factor_eq
          hstart hnext hcapacity horigLength
        have hbaseLengthVal := ProgressiveTree.rebase_layer_length_clamped ValueInst hqueries.factor_eq
          hstart hnext hcapacity hbaseLength
        have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
        have hfullDepthVal := usize_add_val hfullDepth
        have hfullDepthNat : fullDepth.val = 2 * depth.val + packingDepth.val := by omega
        have hnewLeft := tree.Tree.rebase_on_contents_correct_of_inputs ValueInst
          (lengths := some (origLeftLength, baseLeftLength)) (fullDepth := fullDepth)
          (by simpa only [rebaseLengths, Option.map_some, horigLengthVal, hbaseLengthVal, hfullDepthNat]
              using hleftContent) hleft
        have hadd := UScalar.add_equiv depth 1#u32
        rw [hnext] at hadd
        simp at hadd
        have hnextVal : next.val = depth.val + 1 := by omega
        have hnewRight := ih (by simpa only [hnextVal] using hrightContent) hright
        simp only [ProgressiveTree.elements]
        rw [hnewLeft.1, hnewRight]

/-- The public progressive call preserves materialized contents under the
same selected semantic law at depth zero. Global geometry and packing laws
are unnecessary for this content result. -/
theorem ProgressiveTree.rebase_on_preserves_contents_of_inputs {T : Type} (ValueInst : Value T)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (hcontent : orig.RebaseContentInputs ValueInst base origLength.val baseLength.val 0)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) :
    after.elements = orig.elements :=
  ProgressiveTree.rebase_on_recursive_preserves_contents_of_inputs ValueInst hcontent hrebase

end milhouse.progressive_tree
