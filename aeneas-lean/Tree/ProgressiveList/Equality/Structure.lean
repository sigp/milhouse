import Tree.ProgressiveTree.Equality.Lookup
import Tree.ProgressiveList.Backing

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

/-- Equal list structure preserves all backing lookup results without
    representation, packing, or backing-validity assumptions. -/
theorem ProgressiveList.StructuralEq.backing_get_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {updatesEqual : U → U → Prop} {self other : ProgressiveList T U}
    (heq : self.StructuralEq updatesEqual other) (index : Std.Usize) :
    ProgressiveList.backing_get ValueInst mapInst self index =
      ProgressiveList.backing_get ValueInst mapInst other index := by
  simp only [ProgressiveList.backing_get, ProgressiveList.backing_len, heq.2.1,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok,
    heq.1.get_recursive_eq ValueInst]

/-- The full merged lookup computation agrees when related pending maps have
    equal reads. This also covers failed or diverging reads. -/
theorem ProgressiveList.StructuralEq.get_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {updatesEqual : U → U → Prop} {self other : ProgressiveList T U}
    (heq : self.StructuralEq updatesEqual other)
    (hmapGet : updatesEqual self.updates other.updates →
      ∀ query, mapInst.get other.updates query = mapInst.get self.updates query)
    (index : Std.Usize) :
    ProgressiveList.get ValueInst mapInst self index =
      ProgressiveList.get ValueInst mapInst other index := by
  simp only [ProgressiveList.get, hmapGet heq.2.2 index, heq.backing_get_eq ValueInst mapInst]

/-- Structural agreement preserves the represented merged sequence when the
    related pending maps have the same reads and maximum. Direct lookup
    congruence removes all packing and backing-validity premises. -/
theorem ProgressiveList.StructuralEq.represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {updatesEqual : U → U → Prop} {self other : ProgressiveList T U}
    (heq : self.StructuralEq updatesEqual other) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hmapGet : updatesEqual self.updates other.updates →
      ∀ query, mapInst.get other.updates query = mapInst.get self.updates query)
    (hmapMax : updatesEqual self.updates other.updates →
      mapInst.max_index other.updates = mapInst.max_index self.updates) :
    other.Represents ValueInst mapInst contents := by
  obtain ⟨⟨length, hlength, hcontents⟩, hreads⟩ := hrep
  refine ⟨⟨length, ?_, hcontents⟩, ?_⟩
  · simpa only [ProgressiveList.len, utils.updated_length, hmapMax heq.2.2, heq.2.1] using hlength
  · intro query
    rw [← heq.get_eq ValueInst mapInst hmapGet query]
    exact hreads query

end milhouse.progressive_list
