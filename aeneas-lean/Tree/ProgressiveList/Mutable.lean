import Tree.ProgressiveList.Contents
import Tree.UpdateMap.Mutable

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

/-- Mutable access reads the same value as `get`, including `none` at missing
    indices, under the map lookup law and value-preserving element cloning. -/
theorem ProgressiveList.get_mut_reads_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ProgressiveList.get ValueInst mapInst self index = ok value := by
  obtain ⟨mapBack, hmap, _⟩ :=
    ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  have hread := hreads
    (ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption
      ValueInst mapInst) (self.tree, self.length)
  rw [hmap] at hread
  simp only [bind_tc_ok] at hread
  have hfallback :
      ProgressiveList.get_mut.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOption.call_once
        ValueInst mapInst (self.tree, self.length) index =
      ProgressiveList.backing_get ValueInst mapInst self index := by
    rw [ProgressiveList.get_mut_fallback_eq]
    cases ProgressiveList.backing_get ValueInst mapInst self index with
    | fail e => rfl
    | div => rfl
    | ok found => cases found <;> simp [core.option.OptionShared0T.cloned, hclone]
  simp only [hfallback] at hread
  unfold ProgressiveList.get
  cases hpending : mapInst.get self.updates index with
  | fail e => simp [hpending] at hread
  | div => simp [hpending] at hread
  | ok pending =>
    cases pending <;> simpa [hpending] using hread.symm

/-- Writing through a present mutable handle changes only the selected list
    element, including all pending and backing lookups at other indices. -/
theorem ProgressiveList.get_after_get_mut_at {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    (hwrites : update_map.GetMutWithWrites mapInst self.updates index)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.get ValueInst mapInst (back (some replacement)) query =
      if query = index then ok (some replacement)
      else ProgressiveList.get ValueInst mapInst self query := by
  obtain ⟨mapBack, hmap, rfl⟩ :=
    ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  have hget := hwrites _ _ _ _ hmap replacement query
  by_cases hquery : query = index
  · simp only [if_pos hquery] at hget ⊢
    exact ProgressiveList.get_of_pending_update ValueInst mapInst _ query replacement hget
  · simp only [if_neg hquery] at hget ⊢
    simp only [ProgressiveList.get, hget, ProgressiveList.backing_get,
      ProgressiveList.backing_len]

/-- Replacing a borrowed element within the logical bounds preserves length.
    The only new map premise is that mutable access records the selected key
    in its maximum-index metadata. -/
theorem ProgressiveList.len_after_get_mut {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index length : Std.Usize) (replacement : T)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length)
    (hindex : index.val < length.val)
    (hmax : update_map.GetMutWithMaxIndex mapInst self.updates index)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.len ValueInst mapInst (back (some replacement)) = ok length := by
  obtain ⟨mapBack, hmap, rfl⟩ :=
    ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  rw [ProgressiveList.len_eq_updated_length] at hlen ⊢
  exact utils.updated_length_insert_below mapInst self.length self.updates
    (mapBack (some replacement)) index length hlen hindex
    (hmax _ _ _ _ hmap replacement)

/-- **Sequence replacement correctness.** Writing a new value through a
    returned mutable element handle preserves length and every other element.
    The old representation and successful read supply the index bound, so
    callers need no separate bounds or tree invariants. -/
theorem ProgressiveList.get_mut_represents_set {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hwrites : update_map.GetMutWithWrites mapInst self.updates index)
    (hmax : update_map.GetMutWithMaxIndex mapInst self.updates index)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    (back (some replacement)).Represents ValueInst mapInst
      (contents.set index.val replacement) := by
  obtain ⟨⟨length, hlen, hlength⟩, hget⟩ := hrep
  have hread := ProgressiveList.get_mut_reads_get ValueInst mapInst self index hreads hclone hmut
  rw [hget index] at hread
  have hindex : index.val < contents.length := by
    by_contra hout
    have hnone : contents[index.val]? = none :=
      _root_.List.getElem?_eq_none_iff.mpr (by omega)
    simp [hnone] at hread
  refine ⟨⟨length, ProgressiveList.len_after_get_mut ValueInst mapInst self index length
    replacement hlen (by omega) hmax hmut, by simp [hlength]⟩, ?_⟩
  intro query
  rw [ProgressiveList.get_after_get_mut_at ValueInst mapInst self index query replacement
    hwrites hmut]
  by_cases heq : query = index
  · subst query
    simp [hindex]
  · rw [if_neg heq, hget query]
    have hne : index.val ≠ query.val := by
      intro heqval
      apply heq
      scalar_tac
    simp [hne]

end milhouse.progressive_list
