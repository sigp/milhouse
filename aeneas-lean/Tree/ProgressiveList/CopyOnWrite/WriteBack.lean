import Tree.ProgressiveList.CopyOnWrite.Acquisition

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Exact public read criterion after returning a CoW handle. It needs no
filled-entry footprint or write law because every continuation preserves the
backing fields; its returned map alone determines the lookup condition. -/
theorem ProgressiveList.get_after_cow_writeback_eq_iff_lookup {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back)) :
    ProgressiveList.get ValueInst mapInst (back (some changed)) query =
      (if query = index then ok (some replacement) else ProgressiveList.get ValueInst mapInst self query) ↔
      update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
        (mapInst.get (back (some changed)).updates query)
        (if query = index then ok (some replacement) else mapInst.get self.updates query) := by
  obtain ⟨_, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self _ index query replacement

/-- Exact metadata criterion for the full length result after returning a CoW
handle. The backing length is preserved through every continuation, so this
needs no write-footprint, bounds, representation, or successful query law. -/
theorem ProgressiveList.len_after_cow_writeback_eq_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back)) :
    ProgressiveList.len ValueInst mapInst (back (some changed)) =
        ProgressiveList.len ValueInst mapInst self ↔
      utils.MaxIndexResultsAgree self.length
        (mapInst.max_index (back (some changed)).updates) (mapInst.max_index self.updates) := by
  obtain ⟨_, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ProgressiveList.len_with_updates_eq_iff_max_index ValueInst mapInst self _

/-- Exact sequence criterion for a returned CoW continuation. Lookup and
maximum agreement are jointly necessary and sufficient without a write law
or an assumed filled-entry footprint. -/
theorem ProgressiveList.cow_writeback_represents_set_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back)) :
    (back (some changed)).Represents ValueInst mapInst (contents.set index.val replacement) ↔
      utils.MaxIndexResultsAgree self.length
        (mapInst.max_index (back (some changed)).updates) (mapInst.max_index self.updates) ∧
      self.SetReadsAgree ValueInst mapInst (back (some changed)).updates index replacement := by
  obtain ⟨_, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact ProgressiveList.represents_set_with_updates_iff ValueInst mapInst self contents _ index replacement hrep hindex

end milhouse.progressive_list
