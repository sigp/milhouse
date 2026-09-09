import Tree.ProgressiveList.Rebase.Validity

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A list with cleared caches can be rebased in place without any collision
assumption. Construction and the nonzero front-removal proofs establish this
input invariant; base validity covers only caches selected by binary actions
in reached progressive layers. -/
theorem ProgressiveList.rebase_on_total_from_cleared_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hclear : self.tree.CachesCleared)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0) := by
    rw [progressive_tree.ProgressiveTree.rebaseHashInputs_eq_nil_of_cleared self.tree base.tree 0 hclear]
    exact BinaryHashCollisionSoundOn.nil reference
  have hselfCache := hclear.cachesOn (CacheValidFor reference) (CacheValidFor.zero reference) 0
  exact ProgressiveList.rebase_on_total_valid_cache_spec ValueInst mapInst hlayout
    reference self base contents hrep hbacking hbase hequality hcollisions hcompare
    (self.tree.rebaseOrigCachesOn_of_caches ValueInst.corecmpPartialEqInst
      (CacheValidFor reference) base.tree 0 hselfCache)
    (self.tree.rebaseHashCachesOn_of_caches (CacheValidFor reference) base.tree 0 hselfCache)
    hbaseCache

/-- Nonmutating rebasing from cleared caches needs no collision assumption.
It preserves contents and reference cache validity under the ordinary element
comparison and pending-map clone laws. -/
theorem ProgressiveList.rebase_total_from_cleared_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (reference : CacheSubject T → CacheHash)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hclear : self.tree.CachesCleared)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hclone : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      self.UpdateReadsAgree ValueInst mapInst updates)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length)
    (hbaseCache : self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst (CacheValidFor reference) base.tree 0) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates ∧
      result.tree.CachesOn (CacheValidFor reference) 0 := by
  have hcollisions : BinaryHashCollisionSoundOn reference (self.tree.rebaseHashInputs base.tree 0) := by
    rw [progressive_tree.ProgressiveTree.rebaseHashInputs_eq_nil_of_cleared self.tree base.tree 0 hclear]
    exact BinaryHashCollisionSoundOn.nil reference
  have hselfCache := hclear.cachesOn (CacheValidFor reference) (CacheValidFor.zero reference) 0
  exact ProgressiveList.rebase_total_valid_cache_spec ValueInst mapInst hlayout
    reference self base contents hrep hbacking hbase hequality hcollisions hcompare hclone hmapGet hmapMax
    (self.tree.rebaseOrigCachesOn_of_caches ValueInst.corecmpPartialEqInst
      (CacheValidFor reference) base.tree 0 hselfCache)
    (self.tree.rebaseHashCachesOn_of_caches (CacheValidFor reference) base.tree 0 hselfCache)
    hbaseCache

end milhouse.progressive_list
