import Tree.Rebase.SelectedCaches
import Tree.ProgressiveTree.Rebase.SelectedCacheInputs
import Tree.ProgressiveTree.Rebase.SelectedContents
import Tree.ProgressiveTree.Rebase.Ready

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Successful progressive rebasing satisfies exactly its selected input
cache laws under selected content soundness. Actual packing results, clamped
lengths, and child calls are recovered from execution. No global geometry,
layout, query-success, or input-cache-validity premise is assumed. -/
theorem ProgressiveTree.rebase_on_recursive_cache_iff_of_inputs {T : Type} (ValueInst : Value T)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hcontent : orig.RebaseContentInputs ValueInst base origLength.val baseLength.val depth.val)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after)) :
    after.CachesOn P depth.val ↔ orig.RebaseCacheInputs ValueInst P base origLength.val baseLength.val depth.val := by
  induction orig generalizing base after depth with
  | ProgressiveZero =>
    rw [ProgressiveTree.rebase_on_recursive_stop_state ValueInst (Or.inl rfl) hrebase]
    exact (ProgressiveTree.rebaseCacheInputs_iff_of_stop ValueInst P _ _ _ _ _ (Or.inl rfl)).symm
  | ProgressiveNode origHash origLeft origRight ih =>
    rcases ProgressiveTree.rebase_on_recursive_ready ValueInst hrebase with hstop | ⟨factor, packingDepth, hqueries, _⟩
    · rw [ProgressiveTree.rebase_on_recursive_stop_state ValueInst hstop hrebase]
      exact (ProgressiveTree.rebaseCacheInputs_iff_of_stop ValueInst P _ _ _ _ _ hstop).symm
    · cases ProgressiveTree.rebase_on_recursive_step_of_depth_query ValueInst hqueries.depth_eq hrebase with
      | same _ _ hstop =>
        exact (ProgressiveTree.rebaseCacheInputs_iff_of_stop ValueInst P _ _ _ _ _ hstop).symm
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
        have hleftScope : origLeft.RebaseContentInputs ValueInst.corecmpPartialEqInst baseLeft
            (rebaseLengths (some (origLeftLength, baseLeftLength))) fullDepth.val := by
          simpa only [rebaseLengths, Option.map_some, horigLengthVal, hbaseLengthVal, hfullDepthNat] using hleftContent
        have hleftContents := tree.Tree.rebase_on_contents_correct_of_inputs ValueInst
          (lengths := some (origLeftLength, baseLeftLength)) (fullDepth := fullDepth) hleftScope hleft
        have hleftIff := tree.Tree.rebase_on_cache_iff_of_inputs ValueInst P
          (lengths := some (origLeftLength, baseLeftLength)) (fullDepth := fullDepth) (depth := 2 * depth.val)
          hleftScope hleft
        simp only [rebaseLengths, Option.map_some, horigLengthVal, hbaseLengthVal, hfullDepthNat] at hleftIff
        have hadd := UScalar.add_equiv depth 1#u32
        rw [hnext] at hadd
        simp at hadd
        have hnextVal : next.val = depth.val + 1 := by omega
        have hrightScope : origRight.RebaseContentInputs ValueInst baseRight origLength.val baseLength.val next.val := by
          simpa only [hnextVal] using hrightContent
        have hrightContents := ProgressiveTree.rebase_on_recursive_preserves_contents_of_inputs ValueInst hrightScope hright
        have hrightIff := ih hrightScope hright
        simp only [hnextVal] at hrightIff
        simp [ProgressiveTree.CachesOn, ProgressiveTree.RebaseCacheInputs, hpointer]
        rw [hleftContents.1, hrightContents]
        constructor
        · rintro ⟨hroot, hleftCache, hrightCache⟩ actualFactor actualDepth actualQueries
          obtain ⟨rfl, rfl⟩ := actualQueries.unique hqueries
          exact ⟨hroot, hleftIff.mp hleftCache, hrightIff.mp hrightCache⟩
        · intro hcache
          obtain ⟨hroot, hleftCache, hrightCache⟩ := hcache factor packingDepth hqueries
          exact ⟨hroot, hleftIff.mpr hleftCache, hrightIff.mpr hrightCache⟩

/-- Public progressive cache validity is equivalent to the selected input
cache scope at depth zero under only the selected semantic content law. -/
theorem ProgressiveTree.rebase_on_cache_iff_of_inputs {T : Type} (ValueInst : Value T)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (hcontent : orig.RebaseContentInputs ValueInst base origLength.val baseLength.val 0)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) :
    after.CachesOn P 0 ↔ orig.RebaseCacheInputs ValueInst P base origLength.val baseLength.val 0 :=
  ProgressiveTree.rebase_on_recursive_cache_iff_of_inputs ValueInst P hcontent hrebase

end milhouse.progressive_tree
