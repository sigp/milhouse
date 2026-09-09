import Tree.ProgressiveList.Mutable

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Mutable access to a present element succeeds if the one possible fallback
clone succeeds. An existing pending value is returned directly; otherwise the
returned value is the actual clone result, which need not equal the old value. -/
theorem ProgressiveList.get_mut_present_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (old : T)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok (some old))
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone old = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back) ∧
      ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone old = ok value)) := by
  obtain ⟨value, hread, hinitial⟩ : ∃ value,
      (do let (found, _) ← ProgressiveList.get_mut ValueInst mapInst self index
          ok found) = ok (some value) ∧
      ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone old = ok value)) := by
    have hread := ProgressiveList.get_mut_read_eq_pending_or_clone
      ValueInst mapInst self index hreads
    cases hpending : mapInst.get self.updates index with
    | fail e => simp [ProgressiveList.get, hpending] at hget
    | div => simp [ProgressiveList.get, hpending] at hget
    | ok pending =>
      cases pending with
      | none =>
        simp only [ProgressiveList.get, hpending, bind_tc_ok] at hget
        obtain ⟨value, hcloned⟩ := hclone hpending
        refine ⟨value, ?_, Or.inr ⟨rfl, hcloned⟩⟩
        refine hread.trans ?_
        simp only [hpending, bind_tc_ok, hget, core.option.OptionShared0T.cloned,
          hcloned]
      | some pending =>
        have heq : pending = old := by simpa [ProgressiveList.get, hpending] using hget
        subst pending
        refine ⟨old, ?_, Or.inl ⟨rfl, rfl⟩⟩
        refine hread.trans ?_
        simp only [hpending, bind_tc_ok]
  cases hmut : ProgressiveList.get_mut ValueInst mapInst self index with
  | fail e => simp [hmut] at hread
  | div => simp [hmut] at hread
  | ok handle =>
    obtain ⟨found, back⟩ := handle
    simp [hmut] at hread
    subst found
    exact ⟨value, back, rfl, hinitial⟩

/-- Accessing any represented in-bounds element succeeds, and writing through
the returned reference replaces exactly that element while preserving the
backing tree and its recorded length. The initial value is either the pending
element or the actual fallback clone. Only that clone must terminate, and it
need not preserve the old element. No structural backing invariant is needed. -/
theorem ProgressiveList.get_mut_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hwrites : update_map.GetMutWithWrites mapInst self.updates index)
    (hmax : update_map.GetMutWithMaxIndex mapInst self.updates index)
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone contents[index.val] = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back) ∧
      ((mapInst.get self.updates index = ok (some contents[index.val]) ∧ value = contents[index.val]) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone contents[index.val] = ok value)) ∧
      ∀ replacement,
        (back (some replacement)).Represents ValueInst mapInst (contents.set index.val replacement) ∧
        (back (some replacement)).tree = self.tree ∧
        (back (some replacement)).length = self.length := by
  have hget : ProgressiveList.get ValueInst mapInst self index = ok (some contents[index.val]) := by
    rw [hrep.2 index]
    simp [hindex]
  obtain ⟨value, back, hmut, hinitial⟩ := ProgressiveList.get_mut_present_succeeds
    ValueInst mapInst self index contents[index.val] hreads hget hclone
  refine ⟨value, back, hmut, hinitial, ?_⟩
  intro replacement
  refine ⟨ProgressiveList.get_mut_represents_set ValueInst mapInst self contents index replacement
    hrep hreads hwrites hmax hmut, ?_⟩
  obtain ⟨mapBack, hmap, hback⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  rw [hback]
  exact ⟨rfl, rfl⟩

/-- Complete mutable access for every machine index. A missing index returns
no element and leaves the list unchanged. A present index returns the pending
value or its actual backing clone, and subsequent write-back replaces exactly
that element. Cloning, write, and maximum-index laws are required only for
present elements; the missing-handle law is required only out of bounds. -/
theorem ProgressiveList.get_mut_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hwrites : index.val < contents.length → update_map.GetMutWithWrites mapInst self.updates index)
    (hmax : index.val < contents.length → update_map.GetMutWithMaxIndex mapInst self.updates index)
    (hmissing : contents.length ≤ index.val → update_map.GetMutWithMissing mapInst self.updates index)
    (hclone : ∀ old, contents[index.val]? = some old → mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone old = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back) ∧
      match value with
      | none => contents[index.val]? = none ∧ back none = self
      | some value =>
        ∃ old, contents[index.val]? = some old ∧
          ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
           (mapInst.get self.updates index = ok none ∧
            ValueInst.corecloneCloneInst.clone old = ok value)) ∧
          ∀ replacement,
            (back (some replacement)).Represents ValueInst mapInst (contents.set index.val replacement) ∧
            (back (some replacement)).tree = self.tree ∧
            (back (some replacement)).length = self.length := by
  by_cases hindex : index.val < contents.length
  · have hsome : contents[index.val]? = some contents[index.val] := by simp [hindex]
    obtain ⟨value, back, hmut, hinitial, hwrite⟩ := ProgressiveList.get_mut_spec
      ValueInst mapInst self contents index hrep hindex hreads (hwrites hindex) (hmax hindex)
      (hclone contents[index.val] hsome)
    exact ⟨some value, back, hmut, contents[index.val], hsome, hinitial, hwrite⟩
  · have hout : contents.length ≤ index.val := by omega
    obtain ⟨back, hmut, hback⟩ := ProgressiveList.get_mut_out_of_bounds
      ValueInst mapInst self contents index hrep hout hreads (hmissing hout)
    exact ⟨none, back, hmut, _root_.List.getElem?_eq_none_iff.mpr hout, hback⟩

end milhouse.progressive_list
