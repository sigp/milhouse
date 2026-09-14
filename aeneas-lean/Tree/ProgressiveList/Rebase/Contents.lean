import Tree.ProgressiveList.Rebase.Representation
import Tree.ProgressiveTree.Rebase.Contents

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

/-- In-place rebasing preserves the merged list under only the selected
    content laws. Backing validity and layout justify indexed traversal;
    no additional pending-map or clone law is needed. -/
theorem ProgressiveList.rebase_on_spec_of_content_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates := by
  have hnew := ProgressiveList.rebase_on_preserves_backing ValueInst mapInst self base hlayout
    hbacking hbase hrebase
  exact ⟨(ProgressiveList.rebase_on_represents_iff ValueInst mapInst hlayout
      self base contents hbacking hbase hcontent hrebase).mpr hrep,
    hnew, ProgressiveList.rebase_on_preserves_metadata ValueInst mapInst self base hrebase⟩

/-- Nonmutating rebasing preserves the represented list and backing validity
    under the selected content laws.
    Cloning the pending map needs only read agreement after the original backing
    fallback and matching logical extent;
    element cloning and exact identity of the cloned map are unnecessary. -/
theorem ProgressiveList.rebase_spec_of_content_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      self.UpdateReadsAgree ValueInst mapInst updates)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (core.result.Result.Ok result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor := by
  have hclone := (ProgressiveList.rebase_preserves_metadata ValueInst mapInst self base hrebase).2
  exact ⟨(ProgressiveList.rebase_represents_iff ValueInst mapInst hlayout
      self base contents hrep hbacking hbase hcontent hrebase).mpr
        ⟨hmapGet result.updates hclone, hmapMax result.updates hclone⟩,
    ProgressiveList.rebase_preserves_backing ValueInst mapInst self base hlayout hbacking hbase hrebase⟩

/-- In-place rebasing preserves every represented value and full backing
    validity. Equality/cache laws concern the materialized inputs only; no
    additional pending-map or clone law is needed. -/
theorem ProgressiveList.rebase_on_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base =
      ok (core.result.Result.Ok (), result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates := by
  have hcontent := progressive_tree.ProgressiveTree.rebaseContentInputs_of_dense ValueInst hlayout
    (origLength := self.length.val) (baseLength := base.length.val) (depth := 0)
    (by simpa only [progressive_tree.progressiveCapacity_zero, Nat.sub_zero] using hbacking.1)
    (by simpa only [progressive_tree.progressiveCapacity_zero, Nat.sub_zero] using hbase)
    hbacking.2 hequality hhashes
  exact ProgressiveList.rebase_on_spec_of_content_inputs ValueInst mapInst hlayout
    self base contents hrep hbacking hbase hcontent hrebase

/-- Nonmutating rebasing preserves the represented list and backing validity.
    Cloning the pending map needs only read agreement after the original backing
    fallback and matching logical extent;
    element cloning and exact identity of the cloned map are unnecessary. -/
theorem ProgressiveList.rebase_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      self.UpdateReadsAgree ValueInst mapInst updates)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (core.result.Result.Ok result)) :
    result.Represents ValueInst mapInst contents ∧ result.BackingValid factor := by
  have hcontent := progressive_tree.ProgressiveTree.rebaseContentInputs_of_dense ValueInst hlayout
    (origLength := self.length.val) (baseLength := base.length.val) (depth := 0)
    (by simpa only [progressive_tree.progressiveCapacity_zero, Nat.sub_zero] using hbacking.1)
    (by simpa only [progressive_tree.progressiveCapacity_zero, Nat.sub_zero] using hbase)
    hbacking.2 hequality hhashes
  exact ProgressiveList.rebase_spec_of_content_inputs ValueInst mapInst hlayout
    self base contents hrep hbacking hbase hcontent hmapGet hmapMax hrebase

end milhouse.progressive_list
