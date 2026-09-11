import Tree.ProgressiveList.Construction.Total

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- With a finite input and a successful default map, construction succeeds
exactly when each occupied progressive layer has representable capacity. Thus
the bound in the total constructor specifications is also necessary; no bound
on the next unused layer or cloning law is imposed. -/
theorem ProgressiveList.try_from_iter_success_iff_length_fits {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    (∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) ↔ ProgressiveTree.LengthFits factor values.length := by
  constructor
  · rintro ⟨self, hnew⟩
    obtain ⟨_, hlength, _⟩ := ProgressiveList.try_from_iter_contents ValueInst mapInst
      iterInst input values hyields hnew
    obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid ValueInst mapInst
      iterInst input hlayout hnew
    simpa only [hlength] using hdense.lengthFits hfits
  · intro hfits
    obtain ⟨self, hnew, _⟩ := ProgressiveList.try_from_iter_total ValueInst mapInst
      iterInst input values hyields hlayout hfits updates hdefault
    exact ⟨self, hnew⟩

/-- The vector constructor's occupied-layer condition is exact. The concrete
vector supplies its iterator behavior; default-map read and emptiness laws are
unnecessary for this success characterization. -/
theorem ProgressiveList.new_success_iff_length_fits {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    (∃ self, ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self)) ↔
      ProgressiveTree.LengthFits factor values.val.length :=
  ProgressiveList.try_from_iter_success_iff_length_fits ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values)
    hlayout updates hdefault

end milhouse.progressive_list
