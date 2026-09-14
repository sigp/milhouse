import Tree.ProgressiveList.Construction.Total
import Tree.ProgressiveTree.Construction.Trace

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful public iterator construction reflects exactly its consumed
sequence, records the exact count, and installs the actual default map. No
input trace, iterator finiteness, packing, or default-map law is assumed. -/
theorem ProgressiveList.try_from_iter_trace {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) :
    IntoIteratorYields iterInst input self.tree.elements ∧
      self.length.val = self.tree.elements.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  unfold ProgressiveList.try_from_iter at hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨status, hbuild, hnew⟩ := hnew
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hnew
  | Ok result =>
    obtain ⟨output, length⟩ := result
    simp! only [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new, bind_tc_ok] at hnew
    rw [bind_eq_ok_iff] at hnew
    obtain ⟨updates, hdefault, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    obtain ⟨hyields, hlength⟩ := ProgressiveTree.build_from_iter_with_len_trace
      ValueInst iterInst input hbuild
    exact ⟨hyields, hlength, hdefault⟩

/-- Every successful public construction represents its actual consumed
sequence at every index, establishes valid backing and spine, and clears
pending updates. Only packing and the actual default map's empty laws are
required; the finite input sequence is inferred from successful execution. -/
theorem ProgressiveList.try_from_iter_trace_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ index, mapInst.get updates index = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) :
    IntoIteratorYields iterInst input self.tree.elements ∧
      self.Represents ValueInst mapInst self.tree.elements ∧ self.BackingValid factor ∧
      self.SpineValid factor ∧ ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  have hyields := (ProgressiveList.try_from_iter_trace ValueInst mapInst iterInst input hnew).1
  obtain ⟨hrep, hspine, hpending⟩ := ProgressiveList.try_from_iter_spec
    ValueInst mapInst iterInst input self.tree.elements hyields hlayout hdefault hnew
  exact ⟨hyields, hrep,
    ProgressiveList.try_from_iter_backing_valid ValueInst mapInst iterInst input hlayout hnew,
    hspine, hpending⟩

end milhouse.progressive_list
