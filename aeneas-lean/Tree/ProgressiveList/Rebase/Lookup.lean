import Tree.ProgressiveList.Rebase.Backing
import Tree.ProgressiveList.Rebase.SelectedContents
import Tree.ProgressiveList.Iter.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful in-place rebasing preserves each backing lookup. The actual
result's traversal invariant and contents are derived from execution; no
pending-map or represented-sequence law is required. -/
theorem ProgressiveList.rebase_on_backing_get_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result))
    (query : Std.Usize) :
    ProgressiveList.backing_get ValueInst mapInst result query =
      ProgressiveList.backing_get ValueInst mapInst self query := by
  have hnew := ProgressiveList.rebase_on_preserves_backing ValueInst mapInst self base hlayout hbacking hbase hrebase
  have helements := ProgressiveList.rebase_on_preserves_backing_contents ValueInst mapInst self base hcontent hrebase
  rw [ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout result hnew.1 hnew.2 query,
    ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout self hbacking.1 hbacking.2 query,
    helements]

/-- Every public lookup result is unchanged by successful in-place rebasing,
including pending-map failure and divergence and out-of-range lookups. No
representation, pending-map success, or map-content law is assumed. -/
theorem ProgressiveList.rebase_on_get_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result))
    (query : Std.Usize) :
    ProgressiveList.get ValueInst mapInst result query = ProgressiveList.get ValueInst mapInst self query := by
  have hreads := ProgressiveList.rebase_on_backing_get_eq ValueInst mapInst hlayout self base hbacking hbase hcontent hrebase query
  obtain ⟨newTree, _, rfl⟩ := ProgressiveList.rebase_on_success_state ValueInst mapInst self base hrebase
  simp only [ProgressiveList.get, hreads]

/-- A nonmutating rebase preserves a complete lookup result exactly when the
actual cloned map's answer agrees at the original backing fallback. Raw map
answers may differ; no successful map read or representation is assumed. -/
theorem ProgressiveList.rebase_get_eq_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result))
    (query : Std.Usize) :
    ProgressiveList.get ValueInst mapInst result query = ProgressiveList.get ValueInst mapInst self query ↔
      update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
        (mapInst.get result.updates query) (mapInst.get self.updates query) := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  have hreads := ProgressiveList.rebase_on_get_eq ValueInst mapInst hlayout
    { self with updates } base hbacking hbase hcontent hrebased query
  have hupdates := (ProgressiveList.rebase_on_preserves_metadata ValueInst mapInst
    { self with updates } base hrebased).2
  rw [hreads, ProgressiveList.get_with_updates_eq_iff, hupdates]

/-- Fallback-aware agreement with the actual cloned pending map is necessary
and sufficient for preserving all public reads after nonmutating rebasing. -/
theorem ProgressiveList.rebase_reads_eq_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    (∀ query, ProgressiveList.get ValueInst mapInst result query = ProgressiveList.get ValueInst mapInst self query) ↔
      self.UpdateReadsAgree ValueInst mapInst result.updates :=
  forall_congr' (fun query => ProgressiveList.rebase_get_eq_iff ValueInst mapInst hlayout
    self base hbacking hbase hcontent hrebase query)

end milhouse.progressive_list
