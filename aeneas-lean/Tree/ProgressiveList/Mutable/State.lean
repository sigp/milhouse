import Tree.ProgressiveList.Mutable.Contracts

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Mutable access returns the map's value and writes back only its updates
    field. The backing tree and backing length are preserved for every returned
    continuation, without any map laws or representation assumptions. -/
theorem ProgressiveList.get_mut_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ∃ mapBack,
      mapInst.get_mut_with
        (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption
          ValueInst mapInst) self.updates index (self.tree, self.length) =
        ok (value, mapBack) ∧
      back = fun replacement => { self with updates := mapBack replacement } := by
  unfold ProgressiveList.get_mut at hmut
  cases hmap : mapInst.get_mut_with
      (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption
        ValueInst mapInst) self.updates index (self.tree, self.length) with
  | fail e => simp [hmap] at hmut
  | div => simp [hmap] at hmut
  | ok handle =>
    obtain ⟨found, mapBack⟩ := handle
    simp [hmap] at hmut
    obtain ⟨rfl, hback⟩ := hmut
    exact ⟨mapBack, rfl, hback.symm⟩

/-- The mutable fallback is a cloned backing lookup. This equation includes
    out-of-bounds and failing lookups, without requiring a tree invariant. -/
theorem ProgressiveList.get_mut_fallback_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) :
    ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption.call_once
      ValueInst mapInst (self.tree, self.length) index = (do
      let value ← ProgressiveList.backing_get ValueInst mapInst self index
      core.option.OptionShared0T.cloned ValueInst.corecloneCloneInst value) := by
  simp only [ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption.call_once,
    ProgressiveList.backing_get, ProgressiveList.backing_len, utils.Length.as_usize,
    triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok]
  change (if index < self.length then do
      let value ← progressive_tree.ProgressiveTree.get_recursive ValueInst self.tree index 0#u32
      core.option.OptionShared0T.cloned ValueInst.corecloneCloneInst value
    else ok none) = _
  by_cases hindex : index < self.length
  · simp only [if_pos hindex]
  · simp only [if_neg hindex, bind_tc_ok, core.option.OptionShared0T.cloned]

/-- Exact read criterion after releasing a present mutable handle. The
returned map may supply the replacement directly or through the unchanged
backing fallback; no write law, index bound, or representation is assumed. -/
theorem ProgressiveList.get_after_get_mut_eq_iff_lookup {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.get ValueInst mapInst (back (some replacement)) query =
      (if query = index then ok (some replacement) else ProgressiveList.get ValueInst mapInst self query) ↔
      update_map.LookupResultsAgree (ProgressiveList.backing_get ValueInst mapInst self query)
        (mapInst.get (back (some replacement)).updates query)
        (if query = index then ok (some replacement) else mapInst.get self.updates query) := by
  obtain ⟨mapBack, _, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact ProgressiveList.get_with_updates_set_eq_iff ValueInst mapInst self _ index query replacement

/-- Exact metadata criterion for preserving the complete length result after
mutable write-back. No bounds, representation, or successful length-query
premise is needed, and different maxima may describe the same extent. -/
theorem ProgressiveList.len_after_get_mut_eq_iff_max_index {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (replacement : T)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.len ValueInst mapInst (back (some replacement)) =
        ProgressiveList.len ValueInst mapInst self ↔
      utils.MaxIndexResultsAgree self.length
        (mapInst.max_index (back (some replacement)).updates) (mapInst.max_index self.updates) := by
  obtain ⟨mapBack, _, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact ProgressiveList.len_with_updates_eq_iff_max_index ValueInst mapInst self _

/-- A returned mutable continuation represents the selected sequence
replacement exactly under lookup and maximum-result agreement. No map read,
write, or metadata law is assumed in this equivalence. -/
theorem ProgressiveList.get_mut_represents_set_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    (back (some replacement)).Represents ValueInst mapInst (contents.set index.val replacement) ↔
      utils.MaxIndexResultsAgree self.length
        (mapInst.max_index (back (some replacement)).updates) (mapInst.max_index self.updates) ∧
      self.SetReadsAgree ValueInst mapInst (back (some replacement)).updates index replacement := by
  obtain ⟨mapBack, _, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact ProgressiveList.represents_set_with_updates_iff ValueInst mapInst self contents _ index replacement hrep hindex

end milhouse.progressive_list
