import Tree.ProgressiveTree.Rebase.Validity
import Tree.ProgressiveList.Rebase.Caches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful in-place rebasing preserves the backing contents and reference
cache validity. The operational cache-shortcut premise is derived from valid
input caches and collision soundness on the finite corresponding input pairs. -/
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
    (hselfCache : self.tree.CachesOn (CacheValidFor reference) 0)
    (hbaseCache : base.tree.BinaryCachesOn (CacheValidFor reference) 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.tree.elements = self.tree.elements ∧ result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    reference self.tree base.tree 0 hselfCache.binary hbaseCache hcollisions
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
    (hselfCache : self.tree.CachesOn (CacheValidFor reference) 0)
    (hbaseCache : base.tree.BinaryCachesOn (CacheValidFor reference) 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.tree.elements = self.tree.elements ∧ result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    reference self.tree base.tree 0 hselfCache.binary hbaseCache hcollisions
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
    (hselfCache : self.tree.CachesOn (CacheValidFor reference) 0)
    (hbaseCache : base.tree.BinaryCachesOn (CacheValidFor reference) 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    reference self.tree base.tree 0 hselfCache.binary hbaseCache hcollisions
  exact ProgressiveList.rebase_on_total_cache_spec ValueInst mapInst hlayout
    (CacheValidFor reference) self base contents hrep hbacking hbase hequality hhashes hcompare hselfCache hbaseCache

/-- Total nonmutating rebasing preserves the represented sequence, backing
validity, and reference-valid caches. Only the actual pending-map clone must
terminate and preserve reads and maximum; cache-shortcut soundness is derived. -/
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
      ∀ query, mapInst.get updates query = mapInst.get self.updates query)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      mapInst.max_index updates = mapInst.max_index self.updates)
    (hselfCache : self.tree.CachesOn (CacheValidFor reference) 0)
    (hbaseCache : base.tree.BinaryCachesOn (CacheValidFor reference) 0) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hhashes := progressive_tree.ProgressiveTree.cachedHashesAgree_of_valid_caches
    reference self.tree base.tree 0 hselfCache.binary hbaseCache hcollisions
  exact ProgressiveList.rebase_total_cache_spec ValueInst mapInst hlayout
    (CacheValidFor reference) self base contents hrep hbacking hbase hequality hhashes hcompare hclone hmapGet hmapMax
    hselfCache hbaseCache

/-- Returned errors restore the original cache state; successful rebasing
preserves validity using the derived finite collision bridge. -/
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
    (hbaseCache : base.tree.BinaryCachesOn (CacheValidFor reference) 0)
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
      reference self base hself hbase hfit hequality hcollisions hselfCache hbaseCache hrebase).2

end milhouse.progressive_list
