import Tree.ProgressiveList.Arbitrary.Behavior
import Tree.ProgressiveList.Construction.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Successful generation represents the actual generated sequence exactly
when its installed default map preserves that sequence by overlay and logical
extent. Generation and construction supply their actual outcomes; no finite
trace, map law, pending emptiness, or element-consumption law is assumed. -/
theorem ProgressiveList.arbitrary_represents_iff {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) :
    self.Represents ValueInst mapInst self.tree.elements ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim self.tree.elements.length
          (fun index => max (index.val + 1) self.tree.elements.length) = self.tree.elements.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates self.tree.elements self.tree.elements := by
  obtain ⟨values, _, hnew⟩ :=
    (ProgressiveList.arbitrary_success_iff inst ValueInst mapInst input after self).mp hresult
  obtain ⟨helements, _, _⟩ := ProgressiveList.new_contents ValueInst mapInst values hnew
  simpa only [helements] using ProgressiveList.new_represents_iff ValueInst mapInst values hlayout hnew

end milhouse.progressive_list
