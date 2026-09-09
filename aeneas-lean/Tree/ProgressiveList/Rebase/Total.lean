import Tree.ProgressiveTree.Rebase.Success
import Tree.ProgressiveList.Rebase.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- In-place rebasing succeeds from compatible shapes, representable original
layers, and terminating leaf comparisons. It copies the pending map unchanged;
no map operation, element clone, density, or hash law is needed for success. -/
theorem ProgressiveList.rebase_on_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hself : self.tree.Shape factor 0) (hbase : base.tree.Shape factor 0)
    (hfit : self.tree.Fits factor 0)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.length = self.length ∧ result.updates = self.updates := by
  obtain ⟨newTree, htree⟩ := progressive_tree.ProgressiveTree.rebase_on_success ValueInst hlayout
    self.tree base.tree self.length base.length hself hbase hfit hcompare
  refine ⟨{ self with tree := newTree }, ?_, rfl, rfl⟩
  rw [ProgressiveList.rebase_on_eq, htree]
  rfl

/-- Nonmutating rebasing additionally needs only the actual pending-map clone
to terminate. Its output map is exactly that clone and its backing length is
unchanged; no identity or read-preservation law is needed for this result. -/
theorem ProgressiveList.rebase_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hself : self.tree.Shape factor 0) (hbase : base.tree.Shape factor 0)
    (hfit : self.tree.Fits factor 0)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0)
    (hclone : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates := by
  obtain ⟨updates, hclone⟩ := hclone
  obtain ⟨result, hrebase, hlength, hupdates⟩ := ProgressiveList.rebase_on_success ValueInst mapInst
    hlayout { self with updates } base hself hbase hfit hcompare
  refine ⟨result, ?_, hlength, ?_⟩
  · simp! only [ProgressiveList.rebase, ProgressiveList.clone_eq, hclone, bind_tc_ok,
      hrebase, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa only [hupdates] using hclone

/-- Total in-place rebasing preserves every represented value, valid backing,
the recorded length, and the exact pending map. Comparison termination is
scoped to corresponding input leaves, and all internal successes are proved. -/
theorem ProgressiveList.rebase_on_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hequality : self.tree.RebaseEqualitySound ValueInst.corecmpPartialEqInst base.tree)
    (hhashes : self.tree.CachedHashesAgree base.tree)
    (hcompare : self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates := by
  obtain ⟨result, hrebase, _⟩ := ProgressiveList.rebase_on_success ValueInst mapInst hlayout self base
    hbacking.1.shape hbase.shape hbacking.2 hcompare
  exact ⟨result, hrebase, ProgressiveList.rebase_on_spec ValueInst mapInst hlayout
    self base contents hrep hbacking hbase hequality hhashes hrebase⟩

/-- Total nonmutating rebasing preserves the represented sequence and backing
validity. Only the pending-map clone needs to succeed and preserve reads after
the original backing fallback and logical extent. No element clone or exact
map/read/maximum identity is assumed. -/
theorem ProgressiveList.rebase_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
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
          (fun index => max (index.val + 1) self.length.val) = contents.length) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates := by
  obtain ⟨result, hrebase, hlength, hupdates⟩ := ProgressiveList.rebase_success ValueInst mapInst
    hlayout self base hbacking.1.shape hbase.shape hbacking.2 hcompare hclone
  obtain ⟨hresult, hvalid⟩ := ProgressiveList.rebase_spec ValueInst mapInst hlayout
    self base contents hrep hbacking hbase hequality hhashes hmapGet hmapMax hrebase
  exact ⟨result, hrebase, hresult, hvalid, hlength, hupdates⟩

end milhouse.progressive_list
