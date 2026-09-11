import Tree.ProgressiveTree.Construction

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Successful construction materializes the input sequence in the backing
    tree, records its exact length, and creates the default update map.
    This sequence theorem is separate from the geometric invariants needed to
    connect materialized contents to every indexed read. -/
theorem ProgressiveList.try_from_iter_contents {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) :
    self.tree.elements = values ∧ self.length.val = values.length ∧
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
    obtain ⟨helements, hlength⟩ := ProgressiveTree.build_from_iter_with_len_elements
      ValueInst iterInst input values hyields hbuild
    exact ⟨helements, hlength, hdefault⟩

/-- Vector construction needs no separate iterator law: the standard owning
    iterator is proved to yield the supplied vector in order. -/
theorem ProgressiveList.new_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (values : alloc.vec.Vec T) {self : ProgressiveList T U}
    (hnew : ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self)) :
    self.tree.elements = values.val ∧ self.length.val = values.val.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates :=
  ProgressiveList.try_from_iter_contents ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values) hnew

/-- Successful public construction establishes dense, representable backing
    layers without any law about the generic default update map. -/
theorem ProgressiveList.try_from_iter_backing_valid {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) :
    self.tree.Dense factor 0 self.length.val ∧ self.tree.Fits factor 0 := by
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
    obtain ⟨updates, _, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    exact ProgressiveTree.build_from_iter_with_len_valid ValueInst iterInst input hlayout hbuild

end milhouse.progressive_list
