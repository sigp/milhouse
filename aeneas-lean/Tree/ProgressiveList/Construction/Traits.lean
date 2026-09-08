import Tree.ProgressiveList.Construction.Representation

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The SSZ construction trait delegates to the inherent constructor, including
    its failure behavior. This equation concerns the extracted Rust wrapper. -/
theorem ProgressiveList.ssz_try_from_iter_eq {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input) :
    ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
        ValueInst mapInst iterInst input =
      ProgressiveList.try_from_iter ValueInst mapInst iterInst input := rfl

/-- Successful SSZ trait construction represents its input sequence at every
    index, establishes the backing-spine invariant, and has no pending updates.
    The complete constructor proof supplies the geometry and routing bounds. -/
theorem ProgressiveList.ssz_try_from_iter_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ i, mapInst.get updates i = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (core.result.Result.Ok self)) :
    self.Represents ValueInst mapInst values ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  rw [ProgressiveList.ssz_try_from_iter_eq] at hnew
  exact ProgressiveList.try_from_iter_spec ValueInst mapInst iterInst input values hyields hlayout hdefault hnew

end milhouse.progressive_list
