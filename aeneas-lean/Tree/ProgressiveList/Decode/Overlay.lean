import Tree.ProgressiveList.Decode.Backing
import Tree.ProgressiveList.Overlay

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A successful public decoder represents its materialized values exactly
when the actual default map preserves them through its overlay and logical
extent. Empty input needs no packing or metadata law. Pending emptiness is
independent of this sequence criterion. -/
theorem ProgressiveList.from_ssz_bytes_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : bytes.val ≠ [] → tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (.Ok self)) :
    self.Represents ValueInst mapInst self.tree.elements ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim self.tree.elements.length
          (fun index => max (index.val + 1) self.tree.elements.length) = self.tree.elements.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates self.tree.elements self.tree.elements := by
  rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
    ⟨_, hempty⟩ | ⟨hnonempty, _⟩
  · obtain ⟨htree, hlength, _⟩ := ProgressiveList.empty_success_state ValueInst mapInst hempty
    simp only [htree, ProgressiveTree.elements]
    rw [ProgressiveList.represents_nil_iff]
    simp only [hlength, true_and]
    constructor
    · rintro ⟨hmax, hget⟩
      exact ⟨⟨none, hmax, rfl⟩, fun index => ⟨none, hget index, rfl⟩⟩
    · rintro ⟨⟨largest, hmax, hextent⟩, hoverlay⟩
      have hnone : largest = none := by
        cases largest with
        | none => rfl
        | some last => simp at hextent
      refine ⟨by simpa only [hnone] using hmax, ?_⟩
      intro index
      obtain ⟨pending, hget, hvalue⟩ := hoverlay index
      simpa using hget.trans (congrArg ok (by simpa using hvalue))
  · obtain ⟨hbacking, _⟩ := ProgressiveList.from_ssz_bytes_backing
      ValueInst mapInst bytes (hlayout hnonempty) hdecode
    simpa only [hbacking.1.elements_length] using ProgressiveList.represents_iff_overlay_of_length
      ValueInst mapInst (hlayout hnonempty) self self.tree.elements hbacking.1 hbacking.2
      hbacking.1.elements_length.symm

end milhouse.progressive_list
