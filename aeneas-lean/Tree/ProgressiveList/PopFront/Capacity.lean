import Tree.ProgressiveList.PopFront.Length
import Tree.ProgressiveList.PopFront.Success

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A successful nonzero removal certifies representability of every occupied
retained layer. This follows from actual reconstruction and its recorded
count, without clone identity, default-map laws, or an assumed capacity bound. -/
theorem ProgressiveList.length_fits_after_nonzero_pop_front {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    ProgressiveTree.LengthFits factor (contents.drop n.val).length := by
  have hvalid := ProgressiveList.pop_front_preserves_backing
    ValueInst mapInst hlayout self n hbacking hpop
  have hfits := hvalid.1.lengthFits hvalid.2
  rwa [ProgressiveList.backing_length_after_nonzero_pop_front
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop] at hfits

/-- For a nonzero in-bounds removal with terminating retained clones and
default construction, success is equivalent to representability of the
occupied retained layers. No clone identity, default lookup/maximum/emptiness
laws, or unused-successor capacity is required. Zero removal is separately an
unconditional no-op. -/
theorem ProgressiveList.pop_front_nonzero_success_iff_length_fits {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) (hbound : n.val ≤ contents.length)
    (hclone : ∀ value ∈ contents.drop n.val,
      ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    (∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result)) ↔
      ProgressiveTree.LengthFits factor (contents.drop n.val).length := by
  constructor
  · rintro ⟨result, hpop⟩
    exact ProgressiveList.length_fits_after_nonzero_pop_front
      ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
  · intro hfits
    obtain ⟨result, hpop, _, _, _⟩ := ProgressiveList.pop_front_nonzero_success
      ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hbound hclone hfits updates hdefault
    exact ⟨result, hpop⟩

end milhouse.progressive_list
