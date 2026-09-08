import Tree.ProgressiveList.Rebase.Backing
import Tree.ProgressiveTree.Rebase.Contents
import Tree.ProgressiveList.Iter.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Replacing the backing tree with another valid tree representing the same
    materialized sequence preserves the merged list. Pending replacements and
    extensions are already covered by the input representation. -/
theorem ProgressiveList.Represents.with_tree {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    {newTree : progressive_tree.ProgressiveTree T}
    (hnew : ({ self with tree := newTree } : ProgressiveList T U).BackingValid factor)
    (helements : newTree.elements = self.tree.elements) :
    ({ self with tree := newTree } : ProgressiveList T U).Represents ValueInst mapInst contents := by
  refine ⟨hrep.1, ?_⟩
  intro index
  have hreads : ProgressiveList.backing_get ValueInst mapInst { self with tree := newTree } index =
      ProgressiveList.backing_get ValueInst mapInst self index := by
    rw [ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout
      { self with tree := newTree } hnew.1 hnew.2 index,
      ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout self hbacking.1 hbacking.2 index]
    rw [helements]
  simpa only [ProgressiveList.get, hreads] using hrep.2 index

/-- In-place rebasing preserves every represented value and full backing
    validity. Equality/cache laws concern the materialized inputs only; no
    additional pending-map or clone law is needed. -/
theorem ProgressiveList.rebase_on_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.eq x y = ok true → x = y)
    (hneSound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates := by
  have hnew := ProgressiveList.rebase_on_preserves_backing ValueInst mapInst self base hlayout
    hbacking hbase hrebase
  obtain ⟨newTree, htree, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  have helements := progressive_tree.ProgressiveTree.rebase_on_preserves_contents ValueInst hlayout hsound hneSound
    hbacking.1 hbase hbacking.2 hhashes htree
  exact ⟨hrep.with_tree ValueInst mapInst hlayout self contents hbacking hnew helements,
    hnew, rfl, rfl⟩

/-- Nonmutating rebasing preserves the represented list and backing validity.
    Cloning the pending map needs only preservation of reads and maximum;
    element cloning and exact identity of the cloned map are unnecessary. -/
theorem ProgressiveList.rebase_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hsound : ∀ x y, ValueInst.corecmpPartialEqInst.eq x y = ok true → x = y)
    (hneSound : ∀ x y, ValueInst.corecmpPartialEqInst.ne x y = ok false → x = y)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∀ query, mapInst.get updates query = mapInst.get self.updates query)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      mapInst.max_index updates = mapInst.max_index self.updates)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (core.result.Result.Ok result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  have hclonedRep := ProgressiveList.clone_represents ValueInst mapInst self contents hrep hmapGet hmapMax hcloned
  have hclonedBacking := ProgressiveList.clone_preserves_backing ValueInst mapInst self hbacking hcloned
  obtain ⟨updates, hupdates, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  have hresult := ProgressiveList.rebase_on_spec ValueInst mapInst hlayout hsound hneSound
    { self with updates } base contents hclonedRep hclonedBacking hbase hhashes hrebased
  exact ⟨hresult.1, hresult.2.1⟩

end milhouse.progressive_list
