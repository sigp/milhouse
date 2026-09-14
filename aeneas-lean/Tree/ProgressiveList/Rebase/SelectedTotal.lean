import Tree.ProgressiveList.Rebase.Ready
import Tree.ProgressiveList.Rebase.Representation

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- With valid traversal and selected content soundness, successful
sequence-preserving in-place rebasing is equivalent to the complete backing
input criterion. No additional map, comparison, or query law is needed. -/
theorem ProgressiveList.rebase_on_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0) :
    (∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents) ↔
      self.tree.RebaseReady ValueInst base.tree self.length.val base.length.val 0 := by
  constructor
  · rintro ⟨result, hrebase, _⟩
    exact (ProgressiveList.rebase_on_success_iff_ready ValueInst mapInst self base).mp ⟨result, hrebase⟩
  · intro hready
    obtain ⟨result, hrebase⟩ := (ProgressiveList.rebase_on_success_iff_ready ValueInst mapInst self base).mpr hready
    exact ⟨result, hrebase, (ProgressiveList.rebase_on_represents_iff ValueInst mapInst hlayout
      self base contents hbacking hbase hcontent hrebase).mpr hrep⟩

/-- Nonmutating rebase succeeds and preserves the represented sequence
exactly when its backing input is ready and its actual map clone returns
fallback-aware reads and matching logical extent. Both directions recover
the actual calls; no public-operation or intermediate success is assumed. -/
theorem ProgressiveList.rebase_success_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0) :
    (∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents) ↔
      self.tree.RebaseReady ValueInst base.tree self.length.val base.length.val 0 ∧
      ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates ∧
        self.UpdateReadsAgree ValueInst mapInst updates ∧
        ∃ largest, mapInst.max_index updates = ok largest ∧
          largest.elim self.length.val
            (fun index => max (index.val + 1) self.length.val) = contents.length := by
  constructor
  · rintro ⟨result, hrebase, hresult⟩
    have hready := ((ProgressiveList.rebase_success_iff_ready ValueInst mapInst self base).mp ⟨result, hrebase⟩).2
    have hclone := (ProgressiveList.rebase_preserves_metadata ValueInst mapInst self base hrebase).2
    exact ⟨hready, result.updates, hclone,
      (ProgressiveList.rebase_represents_iff ValueInst mapInst hlayout
        self base contents hrep hbacking hbase hcontent hrebase).mp hresult⟩
  · rintro ⟨hready, updates, hclone, hreads, hmax⟩
    obtain ⟨result, hrebase⟩ := (ProgressiveList.rebase_success_iff_ready ValueInst mapInst self base).mpr
      ⟨⟨updates, hclone⟩, hready⟩
    have hactual := (ProgressiveList.rebase_preserves_metadata ValueInst mapInst self base hrebase).2
    have hupdates : result.updates = updates := Result.ok.inj (hactual.symm.trans hclone)
    refine ⟨result, hrebase, (ProgressiveList.rebase_represents_iff ValueInst mapInst hlayout
      self base contents hrep hbacking hbase hcontent hrebase).mpr ?_⟩
    simpa only [hupdates] using And.intro hreads hmax

/-- The complete in-place correctness contract follows from selected input
readiness and content soundness. Geometry/layout justify traversal validity;
the pending map is preserved without any map law. -/
theorem ProgressiveList.rebase_on_total_spec_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    (hready : self.tree.RebaseReady ValueInst base.tree self.length.val base.length.val 0) :
    ∃ result, ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ result.updates = self.updates := by
  obtain ⟨result, hrebase, hresult⟩ := (ProgressiveList.rebase_on_success_represents_iff ValueInst mapInst hlayout
    self base contents hrep hbacking hbase hcontent).mpr hready
  exact ⟨result, hrebase, hresult,
    ProgressiveList.rebase_on_preserves_backing ValueInst mapInst self base hlayout hbacking hbase hrebase,
    ProgressiveList.rebase_on_preserves_metadata ValueInst mapInst self base hrebase⟩

/-- The complete nonmutating contract uses precisely one actual map-clone
outcome with the necessary lookup/extent laws and the selected backing input
criterion. The result records that exact clone; no element clone, raw-map
identity, or assumed internal execution is required. -/
theorem ProgressiveList.rebase_total_spec_of_inputs {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    (hready : self.tree.RebaseReady ValueInst base.tree self.length.val base.length.val 0)
    (hmap : ∃ updates, mapInst.corecloneCloneInst.clone self.updates = ok updates ∧
      self.UpdateReadsAgree ValueInst mapInst updates ∧
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length) :
    ∃ result, ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result) ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.length = self.length ∧ mapInst.corecloneCloneInst.clone self.updates = ok result.updates := by
  obtain ⟨result, hrebase, hresult⟩ := (ProgressiveList.rebase_success_represents_iff ValueInst mapInst hlayout
    self base contents hrep hbacking hbase hcontent).mpr ⟨hready, hmap⟩
  exact ⟨result, hrebase, hresult,
    ProgressiveList.rebase_preserves_backing ValueInst mapInst self base hlayout hbacking hbase hrebase,
    ProgressiveList.rebase_preserves_metadata ValueInst mapInst self base hrebase⟩

end milhouse.progressive_list
