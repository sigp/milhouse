import Tree.ProgressiveList.PopFront.Clones

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful nonzero removal records exactly the retained element count.
Actual execution supplies all clone, default-construction, and builder
successes; no clone identity, default-map semantics, final-capacity bound, or
separately assumed removal bound is needed for this count. -/
theorem ProgressiveList.backing_length_after_nonzero_pop_front {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) {result : ProgressiveList T U}
    (hpop : ProgressiveList.pop_front ValueInst mapInst self n = ok (core.result.Result.Ok (), result)) :
    result.length.val = (contents.drop n.val).length := by
  obtain ⟨_, _, hlength, _, _⟩ := ProgressiveList.pop_front_nonzero_clones
    ValueInst mapInst hlayout self contents n hrep hbacking hnonzero hpop
  exact hlength

end milhouse.progressive_list
