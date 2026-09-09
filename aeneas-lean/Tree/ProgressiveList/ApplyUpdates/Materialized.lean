import Tree.ProgressiveList.ApplyUpdates.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Selected clone preservation makes the materialized backing exactly the
original merged sequence, independently of the installed default map. Every
backing read is derived from the actual rebuilding call; density then identifies
the complete stored sequence, including its length. -/
theorem ProgressiveList.apply_updates_nonempty_backing_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hrange : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      self.tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst self.updates)
        ValueInst mapInst self.updates factor maximum 0#u32)
    (hmaximum : ∀ maximum, mapInst.max_index self.updates = ok maximum →
      update_map.MaximumBoundsValues mapInst self.updates maximum)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor)
    (hempty : mapInst.is_empty self.updates = ok false)
    {result : ProgressiveList T U}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (.Ok (), result)) :
    result.tree.elements = contents := by
  obtain ⟨_, _, hreads⟩ := ProgressiveList.apply_updates_nonempty_backing_spec
    ValueInst mapInst self contents hlayout hclone (fun maximum hmax => (hrange maximum hmax).excludesValues)
    hmaximum hrep hbacking.1.shape (by simpa using hbacking.1.endsAfter) hempty happly
  have hafter := ProgressiveList.apply_updates_preserves_backing ValueInst mapInst self contents
    (fun _ => hlayout) (fun _ => hrange) (fun _ => hmaximum) hrep hbacking happly
  have hlength := ProgressiveList.backing_length_after_nonempty_apply_updates
    ValueInst mapInst self contents hrep hempty happly
  have helementsLength : result.tree.elements.length = contents.length :=
    hafter.1.elements_length.trans hlength
  apply _root_.List.ext_getElem?
  intro index
  by_cases hinside : index < contents.length
  · have hbound : index < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    let query := Std.Usize.ofNatCore index hbound
    have hquery : query.val = index := Usize.ofNatCore_val_eq hbound
    have hget := ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout result hafter.1 hafter.2 query
    simpa only [hquery] using Result.ok.inj (hget.symm.trans (hreads query))
  · rw [_root_.List.getElem?_eq_none (by omega), _root_.List.getElem?_eq_none (by omega)]

end milhouse.progressive_list
