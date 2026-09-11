import Tree.ProgressiveList.PopFront.Clones
import Tree.ProgressiveList.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- After successful nonzero removal, the retained source suffix is
represented exactly when the actual default map overlays the actual cloned
backing to that suffix and its maximum preserves the retained length. Clone
identity and empty/default-map semantics are not assumed. The actual clone
sequence, recorded length, and valid rebuilt backing come from execution. -/
theorem ProgressiveList.pop_front_nonzero_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor) (hnonzero : n ≠ 0#usize)
    {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (.Ok (), result)) :
    result.Represents ValueInst mapInst (contents.drop n.val) ↔
      (∃ largest, mapInst.max_index result.updates = ok largest ∧
        largest.elim (contents.drop n.val).length
          (fun index => max (index.val + 1) (contents.drop n.val).length) = (contents.drop n.val).length) ∧
      ProgressiveListIter.Overlay mapInst result.updates result.tree.elements (contents.drop n.val) := by
  obtain ⟨_, _, hlength, _, hvalid⟩ := ProgressiveList.pop_front_nonzero_clones
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
  simpa only [hlength] using ProgressiveList.represents_iff_overlay_of_length ValueInst mapInst hlayout
    result (contents.drop n.val) hvalid.1 hvalid.2 hlength

end milhouse.progressive_list
