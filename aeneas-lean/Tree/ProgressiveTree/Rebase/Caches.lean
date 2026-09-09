import Tree.ProgressiveTree.HashCache
import Tree.ProgressiveTree.Rebase.Contents
import Tree.Rebase.Caches

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Recursive progressive rebasing preserves contents and all cache
predicates. In particular, retaining a progressive node's hash is justified
by preservation of both its binary layer and its complete right suffix. -/
theorem ProgressiveTree.rebase_on_recursive_cache_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (horig : orig.Dense factor depth.val (origLength.val - progressiveCapacity factor depth.val))
    (hbase : base.Dense factor depth.val (baseLength.val - progressiveCapacity factor depth.val))
    (hfit : orig.Fits factor depth.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (horigCache : orig.CachesOn P depth.val) (hbaseCache : base.BinaryCachesOn P depth.val)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (core.result.Result.Ok after)) :
    after.elements = orig.elements ∧ after.CachesOn P depth.val := by
  induction orig generalizing base after depth with
  | ProgressiveZero =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same => exact ⟨rfl, horigCache⟩
  | ProgressiveNode origHash origLeft origRight ih =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same => exact ⟨rfl, horigCache⟩
    | @node _ baseHash _ baseLeft _ baseRight newRight start capacity binary fullDepth origLeftLength baseLeftLength next
        action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright =>
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
      have hnewLeft := tree.Tree.rebase_on_cache_spec ValueInst hlayout P
        (by omega) horigLeft hbaseLeft hequality.1 hhashes.1 horigCache.2.1 hbaseCache.1 hleft
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      have hnextVal : next.val = depth.val + 1 := by omega
      have horigRight : origRight.Dense factor next.val (origLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using horig.right_remainder
      have hbaseRight : baseRight.Dense factor next.val (baseLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using hbase.right_remainder
      have hnewRight := ih horigRight hbaseRight
        (by simpa only [hnextVal] using hrightFit) hequality.2 hhashes.2
        (by simpa only [hnextVal] using horigCache.2.2)
        (by simpa only [hnextVal] using hbaseCache.2) hright
      refine ⟨?_, ?_, hnewLeft.2, ?_⟩
      · simp only [ProgressiveTree.elements, hnewLeft.1.1, hnewRight.1]
      · simpa only [hnewLeft.1.1, hnewRight.1] using horigCache.1
      · simpa only [hnextVal] using hnewRight.2

/-- Public progressive rebasing preserves the materialized sequence and
every original cache invariant, including retained suffix caches. The base
needs validity only for its binary caches; its progressive caches are never
imported. The base can have a different logical length. -/
theorem ProgressiveTree.rebase_on_cache_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (horig : orig.Dense factor 0 origLength.val) (hbase : base.Dense factor 0 baseLength.val)
    (hfit : orig.Fits factor 0)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (horigCache : orig.CachesOn P 0) (hbaseCache : base.BinaryCachesOn P 0)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength =
      ok (core.result.Result.Ok after)) :
    after.elements = orig.elements ∧ after.CachesOn P 0 := by
  have horig' : orig.Dense factor (0#u32).val (origLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using horig
  have hbase' : base.Dense factor (0#u32).val (baseLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using hbase
  exact ProgressiveTree.rebase_on_recursive_cache_spec ValueInst hlayout P
    horig' hbase' hfit hequality hhashes horigCache hbaseCache hrebase

end milhouse.progressive_tree
