import Tree.ProgressiveTree.Equality.Structure
import Tree.ProgressiveList.Rebase.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The fields compared by derived equality. The pending-map relation is
    explicit: maps may compare equal despite different internal cache state. -/
def ProgressiveList.StructuralEq {T U : Type} (updatesEqual : U → U → Prop)
    (self other : ProgressiveList T U) : Prop :=
  self.tree.StructuralEq other.tree ∧ self.length = other.length ∧
    updatesEqual self.updates other.updates

/-- Equal list structure transports full backing validity. This depends on
    neither the meaning of the pending-map relation nor element comparison. -/
theorem ProgressiveList.StructuralEq.backing {T U : Type} {updatesEqual : U → U → Prop}
    {self other : ProgressiveList T U} {factor : Option Std.Usize}
    (heq : self.StructuralEq updatesEqual other) (hbacking : self.BackingValid factor) :
    other.BackingValid factor := by
  obtain ⟨htree, hlength, _⟩ := heq
  refine ⟨?_, htree.fits hbacking.2⟩
  simpa only [hlength] using htree.dense hbacking.1

/-- Structural agreement preserves the represented merged sequence when the
    related pending maps have the same reads and maximum. The other list's
    backing validity is derived, and literal equality of maps is unnecessary. -/
theorem ProgressiveList.StructuralEq.represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {updatesEqual : U → U → Prop} {self other : ProgressiveList T U}
    (heq : self.StructuralEq updatesEqual other) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hmapGet : updatesEqual self.updates other.updates →
      ∀ query, mapInst.get other.updates query = mapInst.get self.updates query)
    (hmapMax : updatesEqual self.updates other.updates →
      mapInst.max_index other.updates = mapInst.max_index self.updates) :
    other.Represents ValueInst mapInst contents := by
  have hother := heq.backing hbacking
  have hnew : ({ self with tree := other.tree } : ProgressiveList T U).BackingValid factor := by
    simpa only [ProgressiveList.BackingValid, heq.2.1] using hother
  have htreeRep := hrep.with_tree ValueInst mapInst hlayout self contents hbacking hnew
    heq.1.elements_eq.symm
  obtain ⟨⟨length, hlength, hcontents⟩, hreads⟩ := htreeRep
  refine ⟨⟨length, ?_, hcontents⟩, ?_⟩
  · simpa only [ProgressiveList.len, utils.updated_length, hmapMax heq.2.2, heq.2.1] using hlength
  · intro query
    simpa only [ProgressiveList.get, hmapGet heq.2.2 query,
      ProgressiveList.backing_get, ProgressiveList.backing_len, heq.2.1] using hreads query

end milhouse.progressive_list
