import Tree.ProgressiveTree.Rebase.SuccessReflection
import Tree.ProgressiveList.Rebase.Total

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A successful public in-place rebase supplies every selected element
comparison. This reflection needs layout and original capacity, but no shape,
density, represented contents, semantic comparison law, or pending-map law. -/
theorem ProgressiveList.rebase_on_comparisons {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hfit : self.tree.Fits factor 0) {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0 := by
  obtain ⟨newTree, htree, _⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  exact progressive_tree.ProgressiveTree.rebase_on_comparisons ValueInst hlayout hfit htree

/-- Nonmutating success recovers the same comparison scope on the original
backing inputs. The actual pending-map clone leaves both trees and lengths
unchanged, without requiring any law about the cloned map's contents. -/
theorem ProgressiveList.rebase_comparisons {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hfit : self.tree.Fits factor 0) {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
      packingDepth.val self.length.val base.length.val 0 := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  exact ProgressiveList.rebase_on_comparisons ValueInst mapInst hlayout { self with updates } base hfit hrebased

/-- At compatible shapes and representable original layers, in-place rebasing
succeeds exactly when its selected element comparisons terminate. The right
side contains only external element-call conditions, with pointer, hash,
length, and vector short circuits retained; no subcall success is assumed. -/
theorem ProgressiveList.rebase_on_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hself : self.tree.Shape factor 0) (hbase : base.tree.Shape factor 0)
    (hfit : self.tree.Fits factor 0) :
    (∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) ↔
      self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
        packingDepth.val self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase⟩
    exact ProgressiveList.rebase_on_comparisons ValueInst mapInst hlayout self base hfit hrebase
  · intro hcompare
    obtain ⟨result, hrebase, _⟩ := ProgressiveList.rebase_on_success ValueInst mapInst hlayout
      self base hself hbase hfit hcompare
    exact ⟨result, hrebase⟩

/-- Successful nonmutating rebasing additionally requires precisely the actual
pending-map clone to return. No clone identity, lookup/maximum agreement,
element cloning, density, accurate input lengths, or hash soundness is required
by this success criterion; those semantic obligations are separate. -/
theorem ProgressiveList.rebase_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hself : self.tree.Shape factor 0) (hbase : base.tree.Shape factor 0)
    (hfit : self.tree.Fits factor 0) :
    (∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) ↔
      (∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates) ∧
      self.tree.RebaseComparisons ValueInst.corecmpPartialEqInst base.tree factor
        packingDepth.val self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase⟩
    exact ⟨⟨result.updates, (ProgressiveList.rebase_preserves_metadata ValueInst mapInst self base hrebase).2⟩,
      ProgressiveList.rebase_comparisons ValueInst mapInst hlayout self base hfit hrebase⟩
  · rintro ⟨hclone, hcompare⟩
    obtain ⟨result, hrebase, _⟩ := ProgressiveList.rebase_success ValueInst mapInst hlayout
      self base hself hbase hfit hcompare hclone
    exact ⟨result, hrebase⟩

end milhouse.progressive_list
