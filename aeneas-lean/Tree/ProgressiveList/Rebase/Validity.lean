import Tree.ProgressiveTree.Rebase.Validity
import Tree.ProgressiveList.Rebase.Caches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful in-place rebasing preserves the backing contents and reference
cache validity. Original retained-cache validity and original hash-shortcut
validity are separate laws. The latter, selected base validity, and finite
collision soundness establish the operational shortcut premise. -/
theorem ProgressiveList.rebase_on_valid_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U)
    (hself : self.tree.Dense factor 0 self.length.val)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hfit : self.tree.Fits factor 0)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0))
    (hselfCache : self.tree.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    (hselfHashes : self.tree.RebaseHashCachesOn (CacheValidFor reference) base.tree 0)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.tree.elements = self.tree.elements ∧ result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    ValueInst.corecmpPartialEqInst reference self.tree base.tree 0 hselfHashes hbaseCache hcollisions
  exact ProgressiveList.rebase_on_cache_spec ValueInst mapInst hlayout
    (CacheValidFor reference) self base hself hbase hfit hequality hhashes hselfCache hbaseCache hrebase

/-- Nonmutating rebasing preserves backing contents and reference cache
validity under the same finite collision law, without pending-map clone laws. -/
theorem ProgressiveList.rebase_valid_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U)
    (hself : self.tree.Dense factor 0 self.length.val)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hfit : self.tree.Fits factor 0)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0))
    (hselfCache : self.tree.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    (hselfHashes : self.tree.RebaseHashCachesOn (CacheValidFor reference) base.tree 0)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.tree.elements = self.tree.elements ∧ result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    ValueInst.corecmpPartialEqInst reference self.tree base.tree 0 hselfHashes hbaseCache hcollisions
  exact ProgressiveList.rebase_cache_spec ValueInst mapInst hlayout
    (CacheValidFor reference) self base hself hbase hfit hequality hhashes hselfCache hbaseCache hrebase

/-- Total in-place rebasing derives all cache-shortcut obligations from the
input validity invariants and finite reference collision law. The conclusion
also preserves indexed contents, backing validity, length, and the exact map. -/
theorem ProgressiveList.rebase_on_total_valid_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0))
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hselfCache : self.tree.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    (hselfHashes : self.tree.RebaseHashCachesOn (CacheValidFor reference) base.tree 0)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    ValueInst.corecmpPartialEqInst reference self.tree base.tree 0 hselfHashes hbaseCache hcollisions
  exact ProgressiveList.rebase_on_total_cache_spec ValueInst mapInst hlayout
    (CacheValidFor reference) self base contents hrep hbacking hbase hequality hhashes hcompare hselfCache hbaseCache

/-- Total nonmutating rebasing preserves the represented sequence, backing
validity, and reference-valid caches. Only the actual pending-map clone must
terminate, preserve reads after the backing fallback, and match logical extent;
cache-shortcut soundness is derived. -/
theorem ProgressiveList.rebase_total_valid_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0))
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hclone : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      self.UpdateReadsAgree ValueInst mapInst updates)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length)
    (hselfCache : self.tree.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    (hselfHashes : self.tree.RebaseHashCachesOn (CacheValidFor reference) base.tree 0)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    ValueInst.corecmpPartialEqInst reference self.tree base.tree 0 hselfHashes hbaseCache hcollisions
  exact ProgressiveList.rebase_total_cache_spec ValueInst mapInst hlayout
    (CacheValidFor reference) self base contents hrep hbacking hbase hequality hhashes hcompare hclone hmapGet hmapMax
    hselfCache hbaseCache

/-- Returned errors restore the original cache state, requiring full original
validity. That invariant supplies both selected original laws on success;
the finite collision bridge then establishes the hash-shortcut obligations. -/
theorem ProgressiveList.rebase_on_preserves_valid_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U)
    (hself : self.tree.Dense factor 0 self.length.val)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hfit : self.tree.Fits factor 0)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0))
    (hselfCache : self.tree.CachesOn (CacheValidFor reference) 0)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0)
    {status : core.result.Result Unit error.Error} {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (status, result)) :
    result.tree.CachesOn (CacheValidFor reference) 0 := by
  cases status with
  | Err error =>
    rw [ProgressiveList.rebase_on_error_preserves_self ValueInst mapInst self base hrebase]
    exact hselfCache
  | Ok success =>
    cases success
    exact (ProgressiveList.rebase_on_valid_cache_spec ValueInst mapInst hlayout
      reference self base hself hbase hfit hequality hcollisions
      (self.tree.rebaseOrigCachesOn_of_caches ValueInst.corecmpPartialEqInst
        (CacheValidFor reference) base.tree 0 hselfCache)
      (self.tree.rebaseHashCachesOn_of_caches (CacheValidFor reference) base.tree 0 hselfCache)
      hbaseCache hrebase).2

end milhouse.progressive_list
