import Tree.ProgressiveTree.Rebase.Caches
import Tree.ProgressiveList.Rebase.Total

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful in-place rebasing preserves the backing sequence and every
cache invariant. The pending map is irrelevant to this result: no map reads,
clones, or representation assumption are required. Base cache validity covers
only matching progressive layers reached after pointer-identity checks. -/
theorem ProgressiveList.rebase_on_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    (self base : ProgressiveList T U)
    (hself : self.tree.Dense factor 0 self.length.val)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hfit : self.tree.Fits factor 0)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hselfCache : self.tree.CachesOn P 0) (hbaseCache : self.tree.RebaseBaseCachesOn P base.tree 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.tree.elements = self.tree.elements ∧ result.tree.CachesOn P 0 := by
  obtain ⟨newTree, htree, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  exact progressive_tree.ProgressiveTree.rebase_on_cache_spec ValueInst hlayout P
    hself hbase hfit hequality hhashes hselfCache hbaseCache htree

/-- Successful nonmutating rebasing preserves the backing sequence and cache
invariants without a law for the cloned pending map. Its actual clone and
rebase calls are recovered from the successful public execution. -/
theorem ProgressiveList.rebase_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    (self base : ProgressiveList T U)
    (hself : self.tree.Dense factor 0 self.length.val)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hfit : self.tree.Fits factor 0)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hselfCache : self.tree.CachesOn P 0) (hbaseCache : self.tree.RebaseBaseCachesOn P base.tree 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.tree.elements = self.tree.elements ∧ result.tree.CachesOn P 0 := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  exact ProgressiveList.rebase_on_cache_spec ValueInst mapInst hlayout P
    { self with updates } base hself hbase hfit hequality hhashes hselfCache hbaseCache hrebased

/-- Total in-place rebasing preserves the represented list, valid backing,
recorded length, exact pending map, and all cache invariants. The cache
contract adds input invariants only; all internal executions are proved. -/
theorem ProgressiveList.rebase_on_total_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hselfCache : self.tree.CachesOn P 0) (hbaseCache : self.tree.RebaseBaseCachesOn P base.tree 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates ∧
      result.tree.CachesOn P 0 := by
  obtain ⟨result, hrebase, hresult, hvalid, hlength, hupdates⟩ :=
    ProgressiveList.rebase_on_total_spec ValueInst mapInst hlayout
      self base contents hrep hbacking hbase hequality hhashes hcompare
  have hcache := ProgressiveList.rebase_on_cache_spec ValueInst mapInst hlayout P
    self base hbacking.1 hbase hbacking.2 hequality hhashes hselfCache hbaseCache hrebase
  exact ⟨result, hrebase, hresult, hvalid, hlength, hupdates, hcache.2⟩

/-- Total nonmutating rebasing additionally preserves all cache invariants.
The pending-map clone is required only to terminate, preserve reads after the
backing fallback, and match logical extent, as in the sequence specification. -/
theorem ProgressiveList.rebase_total_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hclone : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      self.UpdateReadsAgree ValueInst mapInst updates)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length)
    (hselfCache : self.tree.CachesOn P 0) (hbaseCache : self.tree.RebaseBaseCachesOn P base.tree 0) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates ∧
      result.tree.CachesOn P 0 := by
  obtain ⟨result, hrebase, hresult, hvalid, hlength, hupdates⟩ :=
    ProgressiveList.rebase_total_spec ValueInst mapInst hlayout
      self base contents hrep hbacking hbase hequality hhashes hcompare hclone hmapGet hmapMax
  have hcache := ProgressiveList.rebase_cache_spec ValueInst mapInst hlayout P
    self base hbacking.1 hbase hbacking.2 hequality hhashes hselfCache hbaseCache hrebase
  exact ⟨result, hrebase, hresult, hvalid, hlength, hupdates, hcache.2⟩

end milhouse.progressive_list
