import Tree.ProgressiveList.Arbitrary.Behavior
import Tree.ProgressiveList.Arbitrary.Overlay
import Tree.Arbitrary.Reflection

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Every successful generator call has an actual finite control/element
trace producing precisely the backing sequence, with its exact recorded length
and the actual default map. No trace or external trait law is assumed. -/
theorem ProgressiveList.arbitrary_generated_sequence {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) :
    arbitrary.Generates inst input self.tree.elements after ∧
      self.length.val = self.tree.elements.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  obtain ⟨values, hvector, helements, hlength, hdefault⟩ :=
    ProgressiveList.arbitrary_contents inst ValueInst mapInst input after self hresult
  rw [helements]
  exact ⟨(arbitrary.vector_success_iff_generates inst input after values).mp hvector, hlength, hdefault⟩

/-- Successful generation has its actual finite trace, exact recorded length,
and valid backing/spine. The precise default-map overlay and extent laws
supply indexed representation; pending emptiness supplies only its observer.
The element generator may consume, retain, or replace the input. -/
theorem ProgressiveList.arbitrary_success_spec_of_overlay {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after))
    (hextent : ∃ largest, mapInst.max_index self.updates = ok largest ∧
      largest.elim self.tree.elements.length
        (fun index => max (index.val + 1) self.tree.elements.length) = self.tree.elements.length)
    (hoverlay : ProgressiveListIter.Overlay mapInst self.updates self.tree.elements self.tree.elements)
    (hempty : mapInst.is_empty self.updates = ok true) :
    arbitrary.Generates inst input self.tree.elements after ∧
      self.length.val = self.tree.elements.length ∧
      self.Represents ValueInst mapInst self.tree.elements ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨htrace, hlength, _⟩ :=
    ProgressiveList.arbitrary_generated_sequence inst ValueInst mapInst input after self hresult
  have hbacking := ProgressiveList.arbitrary_backing_valid inst ValueInst mapInst hlayout input after self hresult
  exact ⟨htrace, hlength,
    (ProgressiveList.arbitrary_represents_iff inst ValueInst mapInst hlayout input after self hresult).mpr
      ⟨hextent, hoverlay⟩, hbacking, ⟨hbacking.1.shape, by simpa using hbacking.1.endsAfter⟩,
    ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty⟩

/-- Every successful call represents the sequence actually produced by its
element calls, has valid backing and spine, and has no pending updates when
the default map is empty. Termination and capacity are consequences of success,
and neither a generation trace nor an intermediate successful call is assumed. -/
theorem ProgressiveList.arbitrary_success_spec {T U : Type}
    (inst : arbitrary.Arbitrary T) (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ index, mapInst.get updates index = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    (input after : _root_.arbitrary.unstructured.Unstructured) (self : ProgressiveList T U)
    (hresult : ProgressiveList.Insts.ArbitraryArbitrary.arbitrary inst ValueInst mapInst input =
      ok (.Ok self, after)) :
    arbitrary.Generates inst input self.tree.elements after ∧
      self.length.val = self.tree.elements.length ∧
      self.Represents ValueInst mapInst self.tree.elements ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨_, _, hmap⟩ :=
    ProgressiveList.arbitrary_generated_sequence inst ValueInst mapInst input after self hresult
  obtain ⟨hget, hmax, hempty⟩ := hdefault self.updates hmap
  exact ProgressiveList.arbitrary_success_spec_of_overlay inst ValueInst mapInst hlayout input after self hresult
    ⟨none, hmax, rfl⟩ (fun index => ⟨none, hget index, rfl⟩) hempty

end milhouse.progressive_list
