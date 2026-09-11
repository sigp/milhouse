import Tree.ProgressiveList.Construction
import Tree.ProgressiveList.Overlay

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A successful iterator constructor represents its consumed sequence
exactly when the installed default map preserves that sequence through its
overlay and logical extent. Absent reads/maxima and pending emptiness are
not assumed; construction supplies the actual contents and traversal bounds. -/
theorem ProgressiveList.try_from_iter_represents_iff {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input = ok (.Ok self)) :
    self.Represents ValueInst mapInst values ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates values values := by
  obtain ⟨helements, hlength, _⟩ := ProgressiveList.try_from_iter_contents ValueInst mapInst iterInst input values hyields hnew
  obtain ⟨hdense, hfits⟩ := ProgressiveList.try_from_iter_backing_valid ValueInst mapInst iterInst input hlayout hnew
  simpa only [helements, hlength] using ProgressiveList.represents_iff_overlay_of_length
    ValueInst mapInst hlayout self values hdense hfits hlength

/-- The concrete vector input supplies its own iterator trace. Exact default
map overlay and extent characterize successful vector construction's indexed
contents, allowing redundant entries and maxima below the backing length. -/
theorem ProgressiveList.new_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.new ValueInst mapInst values = ok (.Ok self)) :
    self.Represents ValueInst mapInst values.val ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates values.val values.val :=
  ProgressiveList.try_from_iter_represents_iff ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values) hlayout hnew

/-- The actual vector-conversion trait has the same necessary-and-sufficient
default-map criterion as the inherent vector constructor. -/
theorem ProgressiveList.try_from_vec_represents_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.Insts.CoreConvertTryFromVecError.try_from ValueInst mapInst values = ok (.Ok self)) :
    self.Represents ValueInst mapInst values.val ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim values.val.length (fun index => max (index.val + 1) values.val.length) = values.val.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates values.val values.val :=
  ProgressiveList.new_represents_iff ValueInst mapInst values hlayout hnew

/-- The SSZ iterator-construction trait preserves its consumed values under
exactly the same installed-map overlay and extent conditions. -/
theorem ProgressiveList.ssz_try_from_iter_represents_iff {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (.Ok self)) :
    self.Represents ValueInst mapInst values ↔
      (∃ largest, mapInst.max_index self.updates = ok largest ∧
        largest.elim values.length (fun index => max (index.val + 1) values.length) = values.length) ∧
      ProgressiveListIter.Overlay mapInst self.updates values values :=
  ProgressiveList.try_from_iter_represents_iff ValueInst mapInst iterInst input values hyields hlayout hnew

end milhouse.progressive_list
