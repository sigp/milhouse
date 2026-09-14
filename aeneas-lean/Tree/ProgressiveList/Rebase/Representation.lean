import Tree.ProgressiveList.Rebase.Lookup

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- In-place rebasing preserves and reflects sequence representation because
every public read and the logical-length computation are unchanged. No input
representation or pending-map law is required for this equivalence. -/
theorem ProgressiveList.rebase_on_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase_on ValueInst mapInst self base = ok (.Ok (), result)) :
    result.Represents ValueInst mapInst contents ↔ self.Represents ValueInst mapInst contents := by
  have hreads := ProgressiveList.rebase_on_get_eq ValueInst mapInst hlayout self base hbacking hbase hcontent hrebase
  have hlength := (ProgressiveList.rebase_on_preserves_observers ValueInst mapInst self base hrebase).1
  simp only [ProgressiveList.Represents, hlength, hreads]

/-- A successful nonmutating rebase preserves the represented sequence
exactly when its actual cloned map preserves fallback-aware reads and logical
extent. These map conditions are necessary as well as sufficient; no map
identity, exact maximum, successful read, or separate clone law is assumed. -/
theorem ProgressiveList.rebase_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self base : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hbase : base.tree.Dense factor 0 base.length.val)
    (hcontent : self.tree.RebaseContentInputs ValueInst base.tree self.length.val base.length.val 0)
    {result : ProgressiveList T U}
    (hrebase : ProgressiveList.rebase ValueInst mapInst self base = ok (.Ok result)) :
    result.Represents ValueInst mapInst contents ↔
      self.UpdateReadsAgree ValueInst mapInst result.updates ∧
      ∃ largest, mapInst.max_index result.updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length := by
  obtain ⟨cloned, hcloned, hrebased⟩ := ProgressiveList.rebase_success_state ValueInst mapInst self base hrebase
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hcloned
  have hupdates := (ProgressiveList.rebase_on_preserves_metadata ValueInst mapInst
    { self with updates } base hrebased).2
  rw [ProgressiveList.rebase_on_represents_iff ValueInst mapInst hlayout
    { self with updates } base contents hbacking hbase hcontent hrebased, hupdates]
  exact ProgressiveList.represents_with_updates_iff ValueInst mapInst self contents hrep updates

end milhouse.progressive_list
