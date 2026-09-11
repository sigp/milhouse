import Tree.ProgressiveTree.Rebase.SelectedCaches
import Tree.ProgressiveTree.Rebase.Contents
import Tree.Rebase.Caches
import Tree.ProgressiveTree.Rebase.OriginalCaches

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Recursive progressive rebasing preserves contents and all cache
predicates. Retaining a progressive node's hash is justified by preservation
of both its binary layer and its complete right suffix. Base validity covers
only caches selected by binary action categories within the matching layers
entered after the progressive pointer shortcut. Original validity covers the
retained progressive caches and the original binary caches selected by those
actions. Completed child calls remain available when the parent is reused. -/
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
    (horigCache : orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth.val)
    (hbaseCache : orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth.val)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (core.result.Result.Ok after)) :
    after.elements = orig.elements ∧ after.CachesOn P depth.val := by
  have hcontent := ProgressiveTree.rebaseContentInputs_of_dense ValueInst hlayout
    (origLength := origLength.val) (baseLength := baseLength.val) horig hbase hfit hequality hhashes
  refine ⟨ProgressiveTree.rebase_on_recursive_preserves_contents_of_inputs ValueInst hcontent hrebase, ?_⟩
  apply (ProgressiveTree.rebase_on_recursive_cache_iff_of_inputs ValueInst P hcontent hrebase).mpr
  exact (ProgressiveTree.rebaseCacheInputs_iff_of_dense ValueInst hlayout P
    (origLength := origLength.val) (baseLength := baseLength.val) horig hbase hfit).mpr ⟨horigCache, hbaseCache⟩

/-- Public progressive rebasing preserves the materialized sequence and
establishes cache validity from the retained-original and imported-base laws.
Original caches discarded by replacement need no retention law. The base
needs validity only for selected binary caches in reached progressive layers;
binary no-ops and unused or shared suffixes require no base-cache premise.
Base progressive caches are never imported, and logical lengths may differ. -/
theorem ProgressiveTree.rebase_on_cache_spec {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (horig : orig.Dense factor 0 origLength.val) (hbase : base.Dense factor 0 baseLength.val)
    (hfit : orig.Fits factor 0)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (horigCache : orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base 0)
    (hbaseCache : orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base 0)
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
