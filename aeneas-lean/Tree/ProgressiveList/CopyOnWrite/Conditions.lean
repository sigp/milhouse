import Tree.ProgressiveList.CopyOnWrite.Fallback

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The map's read law at the selected fallback is both necessary and
sufficient for the public handle-data result to agree with `get`. No
representation, clone, termination, or structural invariant is assumed. -/
theorem ProgressiveList.get_cow_read_eq_get_iff_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) :
    ((do let (handle, _) ← ProgressiveList.get_cow ValueInst mapInst self index
         ok (handle.map cow.Cow.value)) = ProgressiveList.get ValueInst mapInst self index) ↔
      self.GetCowReads ValueInst mapInst index := by
  constructor
  · intro hread fallback hselected
    have hproject :
        (do let (handle, _) ← ProgressiveList.get_cow ValueInst mapInst self index
            ok (handle.map cow.Cow.value)) =
        (do let (handle, _) ← mapInst.get_cow_with_value
              ValueInst.corecloneCloneInst self.updates index fallback
            ok (handle.map cow.Cow.value)) := by
      rw [ProgressiveList.get_cow_eq_of_fallback ValueInst mapInst self index fallback hselected]
      cases mapInst.get_cow_with_value ValueInst.corecloneCloneInst self.updates index fallback with
      | fail e => rfl
      | div => rfl
      | ok result => obtain ⟨handle, mapBack⟩ := result; rfl
    have hget : ProgressiveList.get ValueInst mapInst self index =
        (do let pending ← mapInst.get self.updates index
            ok (pending.or fallback)) := by
      unfold ProgressiveList.get
      rcases hselected with ⟨pending, hpending, rfl⟩ | ⟨hpending, hfallback⟩
      · simp [hpending]
      · simp [hpending, hfallback]
    exact hproject.symm.trans (hread.trans hget)
  · exact ProgressiveList.get_cow_read_eq_get_of_fallback ValueInst mapInst self index

/-- Restoring the map at the selected fallback is exactly what unchanged
release of every successful public handle requires. The equivalence includes
missing handles and assumes no read, clone, or representation laws. -/
theorem ProgressiveList.get_cow_read_only_preserves_self_iff_fallback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) :
    (∀ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) →
        back handle = self) ↔ self.GetCowPreserves ValueInst mapInst index := by
  constructor
  · intro hpreserves fallback hselected handle mapBack hmap
    have hcow : ProgressiveList.get_cow ValueInst mapInst self index =
        ok (handle, fun replacement => { self with updates := mapBack replacement }) := by
      rw [ProgressiveList.get_cow_eq_of_fallback ValueInst mapInst self index fallback hselected]
      simp only [hmap, bind_tc_ok]
      rfl
    exact congrArg ProgressiveList.updates (hpreserves _ _ hcow)
  · intro hpreserves handle back hcow
    exact ProgressiveList.get_cow_read_only_preserves_self_of_fallback
      ValueInst mapInst self index hpreserves hcow

end milhouse.progressive_list
