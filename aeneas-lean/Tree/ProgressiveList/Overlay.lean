import Tree.ProgressiveList.Iter.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- For a target whose length equals the recorded backing length, dense
traversal represents it exactly when the pending map overlays the backing
values to that target and its maximum has the same logical extent. Raw map
reads need not be absent, and a maximum below the backing length is allowed.
No pending-emptiness law or represented-sequence premise is assumed. -/
theorem ProgressiveList.represents_iff_overlay_of_length {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hdense : self.tree.Dense factor 0 self.length.val)
    (hfits : self.tree.Fits factor 0)
    (hlength : self.length.val = contents.length) :
    self.Represents ValueInst mapInst contents ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim self.length.val
          (fun index => max (index.val + 1) self.length.val) = contents.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates self.tree.elements contents := by
  constructor
  · intro hrep
    obtain ⟨length, hlen, hvalue⟩ := hrep.1
    rw [ProgressiveList.len_eq_updated_length] at hlen
    obtain ⟨largest, hmax, hextent⟩ := (utils.updated_length_eq_ok_iff mapInst self.length self.updates length).mp hlen
    exact ⟨⟨largest, hmax, hextent.trans hvalue⟩,
      hrep.overlay ValueInst mapInst hlayout self contents hdense hfits⟩
  · rintro ⟨⟨largest, hmax, hextent⟩, hoverlay⟩
    refine ⟨⟨self.length, ?_, hlength⟩, ?_⟩
    · rw [ProgressiveList.len_eq_updated_length]
      exact (utils.updated_length_eq_ok_iff mapInst self.length self.updates self.length).mpr
        ⟨largest, hmax, hextent.trans hlength.symm⟩
    · intro index
      obtain ⟨pending, hget, hvalue⟩ := hoverlay index
      have hbacking := ProgressiveList.backing_get_eq_elements ValueInst mapInst hlayout self hdense hfits index
      cases pending <;> simp [ProgressiveList.get, hget, hbacking, Option.or] at hvalue ⊢ <;> exact hvalue

end milhouse.progressive_list
