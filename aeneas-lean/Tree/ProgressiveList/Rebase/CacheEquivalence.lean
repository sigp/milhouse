import Tree.ProgressiveTree.Rebase.CacheReflection
import Tree.ProgressiveList.Rebase.Caches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The retained-original and imported-base cache laws are jointly necessary
and sufficient for a successful in-place rebase result's cache validity,
under the existing content laws and input geometry. No cache validity,
pending-map law, represented sequence, or assumed internal call is a premise. -/
theorem ProgressiveList.rebase_on_cache_iff {T U : Type}
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
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.tree.CachesOn P 0 ↔
      self.tree.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base.tree 0 ∧
        self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base.tree 0 := by
  obtain ⟨newTree, htree, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  exact progressive_tree.ProgressiveTree.rebase_on_cache_iff ValueInst hlayout P
    hself hbase hfit hequality hhashes htree

/-- The same exact cache criterion holds for successful nonmutating rebasing.
Its actual clone and rebase are recovered from the public result. The cache
criterion needs no pending-map clone, read, maximum, or representation law. -/
theorem ProgressiveList.rebase_cache_iff {T U : Type}
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
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.tree.CachesOn P 0 ↔
      self.tree.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base.tree 0 ∧
        self.tree.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base.tree 0 := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  exact ProgressiveList.rebase_on_cache_iff ValueInst mapInst hlayout P
    { self with updates } base hself hbase hfit hequality hhashes hrebased

end milhouse.progressive_list
